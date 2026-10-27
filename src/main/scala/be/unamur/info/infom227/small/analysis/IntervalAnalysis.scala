package be.unamur.info.infom227.small.analysis

import be.unamur.info.infom227.small.analysis.IntervalAnalysisAbstractValue.{Bottom, Interval, Unknown}
import be.unamur.info.infom227.small.analysis.IntervalNumber.{Integer, NegInf, PosInf}
import be.unamur.info.infom227.small.ast
import be.unamur.info.infom227.small.ast.*
import be.unamur.info.infom227.small.cfg.{Cfg, ProgramPoint}

import scala.util.{Success, Try}

enum IntervalNumber:
  case NegInf
  case Integer(value: Int)
  case PosInf

  def min(other: IntervalNumber): IntervalNumber = {
    (this, other) match {
      case (IntervalNumber.NegInf, _) => IntervalNumber.NegInf
      case (_, IntervalNumber.NegInf) => IntervalNumber.NegInf
      case (IntervalNumber.Integer(left), IntervalNumber.Integer(right)) => IntervalNumber.Integer(left min right)
      case (IntervalNumber.PosInf, right) => right
      case (left, IntervalNumber.PosInf) => left
    }
  }

  def max(other: IntervalNumber): IntervalNumber = {
    (this, other) match {
      case (IntervalNumber.PosInf, _) => IntervalNumber.PosInf
      case (_, IntervalNumber.PosInf) => IntervalNumber.PosInf
      case (IntervalNumber.Integer(left), IntervalNumber.Integer(right)) => IntervalNumber.Integer(left max right)
      case (IntervalNumber.NegInf, right) => right
      case (left, IntervalNumber.NegInf) => left
    }
  }

  override def toString: String = {
    this match {
      case IntervalNumber.NegInf => "-∞"
      case IntervalNumber.Integer(value) => value.toString
      case IntervalNumber.PosInf => "+∞"
    }
  }

enum IntervalAnalysisAbstractValue extends Lattice[IntervalAnalysisAbstractValue]:
  case Unknown
  case Interval(from: IntervalNumber, to: IntervalNumber)
  case Bottom

  override def join(other: IntervalAnalysisAbstractValue): IntervalAnalysisAbstractValue = {
    (this, other) match {
      case (IntervalAnalysisAbstractValue.Bottom, _) => other
      case (_, IntervalAnalysisAbstractValue.Bottom) => this
      case (IntervalAnalysisAbstractValue.Interval(leftFrom: IntervalNumber, leftTo: IntervalNumber), IntervalAnalysisAbstractValue.Interval(rightFrom: IntervalNumber, rightTo: IntervalNumber)) => IntervalAnalysisAbstractValue.interval(leftFrom.min(rightFrom), leftTo.max(rightTo))
      case _ => IntervalAnalysisAbstractValue.Unknown
    }
  }

  override def meet(other: IntervalAnalysisAbstractValue): IntervalAnalysisAbstractValue = {
    (this, other) match {
      case (IntervalAnalysisAbstractValue.Unknown, _) => other
      case (_, IntervalAnalysisAbstractValue.Unknown) => this
      case (IntervalAnalysisAbstractValue.Interval(leftFrom: IntervalNumber, leftTo: IntervalNumber), IntervalAnalysisAbstractValue.Interval(rightFrom: IntervalNumber, rightTo: IntervalNumber)) => IntervalAnalysisAbstractValue.interval(leftFrom.max(rightFrom), leftTo.min(rightTo))
      case _ => IntervalAnalysisAbstractValue.Bottom
    }
  }

  override def toString: String = {
    this match {
      case IntervalAnalysisAbstractValue.Unknown => "U"
      case IntervalAnalysisAbstractValue.Interval(from: IntervalNumber, to: IntervalNumber) => s"[$from, $to]"
      case IntervalAnalysisAbstractValue.Bottom => "⊥"
    }
  }

object IntervalAnalysisAbstractValue:
  def constant(number: IntervalNumber): IntervalAnalysisAbstractValue = {
    IntervalAnalysisAbstractValue.Interval(number, number)
  }

  def interval(from: IntervalNumber, to: IntervalNumber): IntervalAnalysisAbstractValue = {
    (from, to) match {
      case (IntervalNumber.Integer(left), IntervalNumber.Integer(right)) => if (left <= right) {
        IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(left), IntervalNumber.Integer(right))
      } else {
        IntervalAnalysisAbstractValue.Bottom
      }
      case (IntervalNumber.PosInf, IntervalNumber.NegInf) => IntervalAnalysisAbstractValue.Bottom
      case (left, right) => IntervalAnalysisAbstractValue.Interval(left, right)
    }
  }

/*
========================
  FIRST PASS ANALYSIS
========================
 */

class IntervalAnalysis(cfg: Cfg, maxIteration: Int = 5 ) extends ForwardMayAnalyzer[IterationAbstractState[IntervalAnalysisAbstractValue]](cfg):
  override def entryAbstractState(): IterationAbstractState[IntervalAnalysisAbstractValue] = IterationAbstractState(state = AbstractState(cfg.parameters.map { parameter => parameter -> IntervalAnalysisAbstractValue.Unknown }.toMap))

  def evaluateOperation(left: IntervalNumber, operator: ArithmeticBinaryOperator, right: IntervalNumber): Option[IntervalNumber] = {
    (left, operator, right) match {
      case (IntervalNumber.Integer(leftVal), ArithmeticBinaryOperator.Add, IntervalNumber.Integer(rightVal)) => Some(IntervalNumber.Integer(leftVal + rightVal))
      case (IntervalNumber.Integer(leftVal), ArithmeticBinaryOperator.Sub, IntervalNumber.Integer(rightVal)) => Some(IntervalNumber.Integer(leftVal - rightVal))
      case (IntervalNumber.Integer(leftVal), ArithmeticBinaryOperator.Mul, IntervalNumber.Integer(rightVal)) => Some(IntervalNumber.Integer(leftVal * rightVal))
      case (IntervalNumber.Integer(leftVal), ArithmeticBinaryOperator.Div, IntervalNumber.Integer(rightVal)) => if (rightVal == 0) {
        None
      } else {
        Some(IntervalNumber.Integer(leftVal / rightVal))
      }
      case (IntervalNumber.PosInf, ArithmeticBinaryOperator.Add | ArithmeticBinaryOperator.Sub, IntervalNumber.Integer(_)) => Some(IntervalNumber.PosInf)
      case (IntervalNumber.PosInf, ArithmeticBinaryOperator.Mul | ArithmeticBinaryOperator.Div, IntervalNumber.Integer(c)) => if (c > 0) {
        Some(IntervalNumber.PosInf)
      } else if (c < 0) {
        Some(IntervalNumber.NegInf)
      } else {
        None
      }
      case (IntervalNumber.Integer(_), ArithmeticBinaryOperator.Add, IntervalNumber.PosInf) => Some(IntervalNumber.PosInf)
      case (IntervalNumber.Integer(_), ArithmeticBinaryOperator.Sub, IntervalNumber.PosInf) => Some(IntervalNumber.NegInf)
      case (IntervalNumber.Integer(c), ArithmeticBinaryOperator.Mul, IntervalNumber.PosInf) => if (c > 0) {
        Some(IntervalNumber.PosInf)
      } else if (c < 0) {
        Some(IntervalNumber.NegInf)
      } else {
        None
      }
      case (IntervalNumber.Integer(c), ArithmeticBinaryOperator.Div, IntervalNumber.PosInf) => Some(IntervalNumber.Integer(0))
      case (IntervalNumber.PosInf, ArithmeticBinaryOperator.Add, IntervalNumber.PosInf) => Some(IntervalNumber.PosInf)
      case (IntervalNumber.PosInf, ArithmeticBinaryOperator.Sub, IntervalNumber.NegInf) => Some(IntervalNumber.PosInf)
      case (IntervalNumber.NegInf, ArithmeticBinaryOperator.Add | ArithmeticBinaryOperator.Sub, IntervalNumber.Integer(_)) => Some(IntervalNumber.NegInf)
      case (IntervalNumber.NegInf, ArithmeticBinaryOperator.Mul | ArithmeticBinaryOperator.Div, IntervalNumber.Integer(c)) => if (c > 0) {
        Some(IntervalNumber.NegInf)
      } else if (c < 0) {
        Some(IntervalNumber.PosInf)
      } else {
        None
      }
      case (IntervalNumber.Integer(_), ArithmeticBinaryOperator.Add, IntervalNumber.NegInf) => Some(IntervalNumber.NegInf)
      case (IntervalNumber.Integer(_), ArithmeticBinaryOperator.Sub, IntervalNumber.NegInf) => Some(IntervalNumber.PosInf)
      case (IntervalNumber.Integer(c), ArithmeticBinaryOperator.Mul, IntervalNumber.NegInf) => if (c > 0) {
        Some(IntervalNumber.NegInf)
      } else if (c < 0) {
        Some(IntervalNumber.PosInf)
      } else {
        None
      }
      case (IntervalNumber.Integer(c), ArithmeticBinaryOperator.Div, IntervalNumber.NegInf) => Some(IntervalNumber.Integer(0))
      case (IntervalNumber.NegInf, ArithmeticBinaryOperator.Add, IntervalNumber.NegInf) => Some(IntervalNumber.NegInf)
      case (IntervalNumber.NegInf, ArithmeticBinaryOperator.Sub, IntervalNumber.PosInf) => Some(IntervalNumber.NegInf)
      case _ => None
    }
  }

  final override def analyseStatement(abstractState: IterationAbstractState[IntervalAnalysisAbstractValue], statement: Statement): IterationAbstractState[IntervalAnalysisAbstractValue] = {
    statement match {
      case AssignStatement(lineNumber, variable, expression) =>
        expression match {
          case ArithmeticConstant(c) => abstractState(variable -> IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(c), IntervalNumber.Integer(c)))
          case Variable(y) => abstractState(variable -> abstractState(y))
          case ArrayLit(elems) =>
            abstractState(variable -> IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(elems.length), IntervalNumber.Integer(elems.length)))
          case ArithmeticBinaryOperation(left: (Variable | ArithmeticConstant), operator, right: (Variable | ArithmeticConstant)) =>
            val leftAbstractValue = left match {
              case Variable(y) => abstractState(y)
              case ArithmeticConstant(c) => IntervalAnalysisAbstractValue.constant(IntervalNumber.Integer(c))
            }
            val rightAbstractValue = right match {
              case Variable(z) => abstractState(z)
              case ArithmeticConstant(c) => IntervalAnalysisAbstractValue.constant(IntervalNumber.Integer(c))
            }
            (leftAbstractValue, rightAbstractValue) match {
              case (IntervalAnalysisAbstractValue.Interval(leftFrom, leftTo), IntervalAnalysisAbstractValue.Interval(rightFrom, rightTo)) =>
                (evaluateOperation(leftFrom, operator, rightFrom), evaluateOperation(leftTo, operator, rightTo)) match {
                  case (Some(newFrom), Some(newTo)) => abstractState(variable -> IntervalAnalysisAbstractValue.Interval(newFrom, newTo))
                  case (_, _) => abstractState(variable -> IntervalAnalysisAbstractValue.Unknown)
                }
              case (_, _) => abstractState(variable -> IntervalAnalysisAbstractValue.Unknown)
            }
          case _ =>
            abstractState(variable -> IntervalAnalysisAbstractValue.Unknown)
        }
      case _ =>
        abstractState
    }
  }

  final override def conditionUpdate(abstractState: IterationAbstractState[IntervalAnalysisAbstractValue], condition: BooleanExpression): Option[IterationAbstractState[IntervalAnalysisAbstractValue]] = {
    condition match {
      case BooleanConstant(true) =>
        Some(abstractState)
      case BooleanConstant(false) =>
        None
      case IntegerComparisonOperation(Variable(x), EqualComparisonOperator.Eq, ArithmeticConstant(c)) =>
        abstractState(x).meet(IntervalAnalysisAbstractValue.constant(Integer(c))) match {
          case IntervalAnalysisAbstractValue.Bottom => None // Condition non satisfaite, on ignore
          case value => Some(abstractState(x -> value))
        }
      case IntegerComparisonOperation(ArithmeticConstant(c), EqualComparisonOperator.Eq, Variable(x)) =>
        abstractState(x).meet(IntervalAnalysisAbstractValue.constant(Integer(c))) match {
          case Bottom => None
          case value => Some(abstractState(x -> value))
        }
      case IntegerComparisonOperation(Variable(x), EqualComparisonOperator.Eq, Variable(y)) =>
        abstractState(x).meet(abstractState(y)) match {
          case IntervalAnalysisAbstractValue.Bottom => None
          case value => Some(abstractState(x -> value)(y -> value))
        }
      case IntegerComparisonOperation(Variable(x), operator: IntegerComparisonOperator, ArithmeticConstant(c)) =>
        val validRange = operator match {
          case IntegerComparisonOperator.Lt => IntervalAnalysisAbstractValue.Interval(IntervalNumber.NegInf, IntervalNumber.Integer(c - 1))
          case IntegerComparisonOperator.Lte => IntervalAnalysisAbstractValue.Interval(IntervalNumber.NegInf, IntervalNumber.Integer(c))
          case IntegerComparisonOperator.Gt => IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(c + 1), IntervalNumber.PosInf)
          case IntegerComparisonOperator.Gte => IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(c), IntervalNumber.PosInf)
        }
        abstractState(x).meet(validRange) match {
          case IntervalAnalysisAbstractValue.Bottom => None
          case value => Some(abstractState(x -> value))
        }
      case IntegerComparisonOperation(ArithmeticConstant(c), operator: IntegerComparisonOperator, Variable(x)) =>
        val validRange = operator match {
          case IntegerComparisonOperator.Lt => IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(c + 1), IntervalNumber.PosInf)
          case IntegerComparisonOperator.Lte => IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(c), IntervalNumber.PosInf)
          case IntegerComparisonOperator.Gt => IntervalAnalysisAbstractValue.Interval(IntervalNumber.NegInf, IntervalNumber.Integer(c - 1))
          case IntegerComparisonOperator.Gte => IntervalAnalysisAbstractValue.Interval(IntervalNumber.NegInf, IntervalNumber.Integer(c))
        }
        abstractState(x).meet(validRange) match {
          case IntervalAnalysisAbstractValue.Bottom => None
          case value => Some(abstractState(x -> value))
        }

      // x < y : [-inf, yHigh -1] [xLow +1, +inf]
      case IntegerComparisonOperation(Variable(x), IntegerComparisonOperator.Lt, Variable(y)) =>
        (abstractState(x), abstractState(y)) match {
          case (Interval(xFrom, xTo), Interval(yFrom, yTo)) =>
            val newX = abstractState(x).meet(
              Interval(NegInf, yTo match {
                case Integer(v) => Integer(v - 1)
                case other => other
              })
            )
            val newY = abstractState(y).meet(
              Interval(xFrom match {
                case Integer(v) => Integer(v + 1)
                case other => other
              }, PosInf)
            )

            (newX, newY) match {
              case (IntervalAnalysisAbstractValue.Bottom, _) => None
              case (_, IntervalAnalysisAbstractValue.Bottom) => None
              case _ => Some(abstractState(x -> newX)(y -> newY))
            }
          case _ => Some(abstractState)
        }

      // x <= y : [-inf, yHigh] [xHigh, +inf]
      case IntegerComparisonOperation(Variable(x), IntegerComparisonOperator.Lte, Variable(y)) =>
        (abstractState(x), abstractState(y)) match {
          case (Interval(xFrom, xTo), Interval(yFrom, yTo)) =>
            val newX = abstractState(x).meet(Interval(NegInf, yTo))
            val newY = abstractState(y).meet(Interval(xFrom, PosInf))

            (newX, newY) match {
              case (IntervalAnalysisAbstractValue.Bottom, _) => None
              case (_, IntervalAnalysisAbstractValue.Bottom) => None
              case _ => Some(abstractState(x -> newX)(y -> newY))
            }
          case _ => Some(abstractState)
        }

      // x > y : [yHigh +1, +inf] [-inf, xHigh -1]
      case IntegerComparisonOperation(Variable(x), IntegerComparisonOperator.Gt, Variable(y)) =>
        (abstractState(x), abstractState(y)) match {
          case (Interval(xFrom, xTo), Interval(yFrom, yTo)) =>
            val newX = abstractState(x).meet(
              Interval(
                yFrom match {
                  case IntervalNumber.Integer(v) => IntervalNumber.Integer(v + 1)
                  case other => other
                },
                PosInf
              )
            )
            val newY = abstractState(y).meet(
              Interval(
                NegInf,
                xTo match {
                  case IntervalNumber.Integer(v) => IntervalNumber.Integer(v - 1)
                  case other => other
                }
              )
            )

            (newX, newY) match {
              case (IntervalAnalysisAbstractValue.Bottom, _) => None
              case (_, IntervalAnalysisAbstractValue.Bottom) => None
              case _ => Some(abstractState(x -> newX)(y -> newY))
            }
          case _ => Some(abstractState)
        }

      // x >= y : [yLow, +inf] [-inf, xHigh]
      case IntegerComparisonOperation(Variable(x), IntegerComparisonOperator.Gte, Variable(y)) =>
        (abstractState(x), abstractState(y)) match {
          case (Interval(xFrom, xTo), Interval(yFrom, yTo)) =>
            val newX = abstractState(x).meet(Interval(yFrom, PosInf))
            val newY = abstractState(y).meet(Interval(NegInf, xTo))

            (newX, newY) match {
              case (IntervalAnalysisAbstractValue.Bottom, _) => None
              case (_, IntervalAnalysisAbstractValue.Bottom) => None
              case _ => Some(abstractState(x -> newX)(y -> newY))
            }
          case _ => Some(abstractState)
        }

      case IntegerComparisonOperation(Variable(x), EqualComparisonOperator.Ne, Variable(y)) =>
        (abstractState(x), abstractState(y)) match {
          case (Interval(xFrom, xTo), Interval(yFrom, yTo))
            if xFrom == xTo && yFrom == yTo && xFrom == yFrom => None
          case _ =>
            Some(abstractState)
        }
      case IntegerComparisonOperation(Variable(x), EqualComparisonOperator.Ne, ArithmeticConstant(c)) =>
        abstractState(x) match {
          case Interval(Integer(from), Integer(to))
            if from == c && to == c => None
          case _ =>
            Some(abstractState)
        }
      case IntegerComparisonOperation(ArithmeticConstant(c), EqualComparisonOperator.Ne, Variable(x)) =>
        abstractState(x) match {
          case Interval(Integer(from), Integer(to))
            if from == c && to == c => None
          case _ =>
            Some(abstractState)
        }
      case _ =>
        Some(abstractState)
    }
  }

  override def merge(analysisState: AnalysisState[IterationAbstractState[IntervalAnalysisAbstractValue]], node: ProgramPoint, left: IterationAbstractState[IntervalAnalysisAbstractValue], right: IterationAbstractState[IntervalAnalysisAbstractValue]): Try[IterationAbstractState[IntervalAnalysisAbstractValue]] = {
    var tryWiden = false

    val joined = left.joinWith(
      right,
      (leftValue, rightValue, iterations) => {
        (leftValue, rightValue) match {
          case (
            IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(a), IntervalNumber.Integer(b)),
            IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(c), IntervalNumber.Integer(d))
          ) =>
            if (iterations.getOrElse(node, 0) > maxIteration) {
              IntervalAnalysisAbstractValue.interval(
                if (a <= c) IntervalNumber.Integer(a) else IntervalNumber.NegInf,
                if (b >= d) IntervalNumber.Integer(b) else IntervalNumber.PosInf
              )
            } else {
              tryWiden = true
              leftValue.join(rightValue)
            }
          case (_, _) => leftValue.join(rightValue)
        }
      }
    )

    Success(
      if (tryWiden) {
        joined.increased(node)
      } else {
        joined
      }
    )
  }


/*
========================
  SECOND PASS ANALYSIS
========================
 */

enum DiagnosticType:
  case Warning
  case Error

case class IntervalInterpreterAbstractState(diagnostics: Set[(DiagnosticType, String)] = Set()) extends Lattice[IntervalInterpreterAbstractState]:
  def addDiagnostic(diagnosticType: DiagnosticType, message: String): IntervalInterpreterAbstractState = {
    IntervalInterpreterAbstractState(diagnostics + ((diagnosticType, message)))
  }

  override def join(other: IntervalInterpreterAbstractState): IntervalInterpreterAbstractState = {
    IntervalInterpreterAbstractState(diagnostics ++ other.diagnostics)
  }

  override def meet(other: IntervalInterpreterAbstractState): IntervalInterpreterAbstractState = {
    IntervalInterpreterAbstractState(diagnostics.intersect(other.diagnostics))
  }

class IntervalAnalysisInterpreter(cfg: Cfg, intervalAnalysisState: AnalysisState[IterationAbstractState[IntervalAnalysisAbstractValue]]) extends ForwardMayAnalyzer[IntervalInterpreterAbstractState](cfg):
  override def entryAbstractState(): IntervalInterpreterAbstractState = IntervalInterpreterAbstractState()

  private def checkAccess(acc: IntervalInterpreterAbstractState, line: Int, array: String, index: IntervalAnalysisAbstractValue, size: IntervalAnalysisAbstractValue): IntervalInterpreterAbstractState = {
    (index, size) match {
      case (IntervalAnalysisAbstractValue.Bottom, _) => acc
      case (IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(lo), IntervalNumber.Integer(hi)), IntervalAnalysisAbstractValue.Interval(IntervalNumber.Integer(nLo), IntervalNumber.Integer(nHi))) =>
        if (hi < 0 || lo >= nHi) acc.addDiagnostic(DiagnosticType.Error, s"Out-of-bounds access to $array at line $line")
        else if (lo >= 0 && hi < nLo) acc
        else acc.addDiagnostic(DiagnosticType.Warning, s"Potential out-of-bounds access to $array at line $line")
      case _ =>
        acc.addDiagnostic(DiagnosticType.Warning, s"Cannot verify access to $array at line $line")
    }
  }

  override def analyseStatement(abstractState: IntervalInterpreterAbstractState, statement: Statement): IntervalInterpreterAbstractState = {
    intervalAnalysisState.abstractStates.get(ProgramPoint.StatementPoint(statement)) match {
      case Some(state) =>
        statement match {
          // Assign Statement
          case AssignStatement(line, _, ArrayAccess(Variable(a), Variable(i))) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))

          // Arith Assign
          case AssignStatement(line, _, ArithmeticBinaryOperation(_, _, ArrayAccess(Variable(a), Variable(i)))) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))
          case AssignStatement(line, _, ArithmeticBinaryOperation(ArrayAccess(Variable(a), Variable(i)), _, _)) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))

          // Boolean Assign
          case AssignStatement(line, _, BooleanBinaryOperation(_, _, ArrayAccess(Variable(a), Variable(i)))) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))
          case AssignStatement(line, _, BooleanBinaryOperation(ArrayAccess(Variable(a), Variable(i)), _, _)) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))

          // Return Statement
          case ReturnStatement(line, ArrayAccess(Variable(a), Variable(i))) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))
          case ReturnStatement(line, ArithmeticBinaryOperation(_, _, ArrayAccess(Variable(a), Variable(i)))) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))
          case ReturnStatement(line, ArithmeticBinaryOperation(ArrayAccess(Variable(a), Variable(i)), _, _)) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))
          case ReturnStatement(line, BooleanBinaryOperation(_, _, ArrayAccess(Variable(a), Variable(i)))) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))
          case ReturnStatement(line, BooleanBinaryOperation(ArrayAccess(Variable(a), Variable(i)), _, _)) =>
            checkAccess(abstractState, line, a, Try(state(i)).getOrElse(Unknown), Try(state(a)).getOrElse(Unknown))

          case _ => abstractState
        }
      case None => abstractState
    }
  }

  override def conditionUpdate(abstractState: IntervalInterpreterAbstractState, condition: BooleanExpression): Option[IntervalInterpreterAbstractState] = {
    Some(abstractState)
  }
