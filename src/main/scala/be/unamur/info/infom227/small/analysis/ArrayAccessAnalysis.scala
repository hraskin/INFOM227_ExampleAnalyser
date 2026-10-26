package be.unamur.info.infom227.small.analysis

import be.unamur.info.infom227.small.analysis.ArrayAbstractValue.{Interval, Unknown}
import be.unamur.info.infom227.small.ast.*
import be.unamur.info.infom227.small.cfg.{Cfg, ProgramPoint}

import scala.util.Try

enum ArrayAbstractValue extends Lattice[ArrayAbstractValue]:
  case Unknown
  case Interval(lower: Double, upper: Double)
  case Bottom

  override def join(other: ArrayAbstractValue): ArrayAbstractValue = {
    (this, other) match {
      case (Bottom, _) => other
      case (_, Bottom) => this
      case (Interval(a, b), Interval(c, d)) =>
        val lo = math.min(a, c)
        val hi = math.max(b, d)
        if (lo > hi) Bottom
        else Interval(lo, hi)
      case _ => Unknown
    }
  }

  override def meet(other: ArrayAbstractValue): ArrayAbstractValue = {
    (this, other) match {
      case (Unknown, _) => other
      case (_, Unknown) => this
      case (Interval(a, b), Interval(c, d)) =>
        val lo = math.max(a, c)
        val hi = math.min(b, d)
        if (lo > hi) Bottom
        else Interval(lo, hi)
      case _ => Bottom
    }
  }

  override def toString: String = {
    this match {
      case Unknown => "U"
      case Bottom => "⊥"
      case Interval(a, b) => s"[$a, $b]"
    }
  }

class ArrayAccessAnalysis(cfg: Cfg) extends ForwardMayAnalyzer[AbstractState[ArrayAbstractValue]](cfg):
  override def entryAbstractState(): AbstractState[ArrayAbstractValue] = AbstractState(cfg.parameters.map { parameter => parameter -> Unknown }.toMap)

  final override def analyseStatement(abstractState: AbstractState[ArrayAbstractValue], statement: Statement): AbstractState[ArrayAbstractValue] = {
    statement match {
      case AssignStatement(lineNumber, variable, expression) =>
        expression match {
          case ArithmeticConstant(c) =>
            abstractState(variable -> Interval(c, c))
          case Variable(v) =>
            abstractState(variable -> abstractState(v))
          case ArithmeticBinaryOperation(Variable(v), ArithmeticBinaryOperator.Add, ArithmeticConstant(c)) =>
            abstractState(v) match {
              case Interval(low, up) =>
                abstractState(variable -> Interval(low + c, up + c))
              case other =>
                abstractState(variable -> other)
            }
          case ArrayLit(elems) =>
            abstractState(variable -> Interval(elems.length, elems.length))
          case _ =>
            abstractState(variable -> Unknown)
        }
      case _ =>
        abstractState
    }
  }

  final override def conditionUpdate(abstractState: AbstractState[ArrayAbstractValue], condition: BooleanExpression): Option[AbstractState[ArrayAbstractValue]] = {
    condition match {
      case IntegerComparisonOperation(Variable(v), IntegerComparisonOperator.Lt, ArithmeticConstant(c)) =>
        abstractState(v).meet(Interval(Double.NegativeInfinity, c.toDouble - 1)) match {
          case ArrayAbstractValue.Bottom => None
          case refined => Some(abstractState(v -> refined))
        }
      case IntegerComparisonOperation(Variable(v), IntegerComparisonOperator.Gte, ArithmeticConstant(c)) =>
        abstractState(v).meet(Interval(c.toDouble, Double.PositiveInfinity)) match {
          case ArrayAbstractValue.Bottom => None
          case refined => Some(abstractState(v -> refined))
        }
      case _ =>
        Some(abstractState)
    }
  }


enum DiagnosticType:
  case Warning
  case Error

case class ArrayInterpreterAbstractState(diagnostics: Set[(DiagnosticType, String)] = Set()) extends Lattice[ArrayInterpreterAbstractState]:
  def addDiagnostic(diagnosticType: DiagnosticType, message: String): ArrayInterpreterAbstractState = {
    ArrayInterpreterAbstractState(diagnostics + ((diagnosticType, message)))
  }

  override def join(other: ArrayInterpreterAbstractState): ArrayInterpreterAbstractState = {
    ArrayInterpreterAbstractState(diagnostics ++ other.diagnostics)
  }

  override def meet(other: ArrayInterpreterAbstractState): ArrayInterpreterAbstractState = {
    ArrayInterpreterAbstractState(diagnostics.intersect(other.diagnostics))
  }

class ArrayAnalysisInterpreter(cfg: Cfg, arrayAccessAnalysisState: AnalysisState[AbstractState[ArrayAbstractValue]]) extends ForwardMayAnalyzer[ArrayInterpreterAbstractState](cfg):
  override def entryAbstractState(): ArrayInterpreterAbstractState = ArrayInterpreterAbstractState()

  private def checkAccess(acc: ArrayInterpreterAbstractState, line: Int, array: String, index: ArrayAbstractValue, size: ArrayAbstractValue): ArrayInterpreterAbstractState = {
    (index, size) match {
      case (ArrayAbstractValue.Bottom, _) => acc
      case (Interval(lo, hi), Interval(nLo, nHi)) =>
        if (hi < 0 || lo >= nHi) acc.addDiagnostic(DiagnosticType.Error, s"Out-of-bounds access to $array at line $line")
        else if (lo >= 0 && hi < nLo) acc
        else acc.addDiagnostic(DiagnosticType.Warning, s"Potential out-of-bounds access to $array at line $line")
      case _ =>
        acc.addDiagnostic(DiagnosticType.Warning, s"Cannot verify access to $array at line $line")
    }
  }

  override def analyseStatement(abstractState: ArrayInterpreterAbstractState, statement: Statement): ArrayInterpreterAbstractState = {
    arrayAccessAnalysisState.abstractStates.get(ProgramPoint.StatementPoint(statement)) match {
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

  override def conditionUpdate(abstractState: ArrayInterpreterAbstractState, condition: BooleanExpression): Option[ArrayInterpreterAbstractState] = {
    Some(abstractState)
  }
