package be.unamur.info.infom227.small.analysis

import be.unamur.info.infom227.small.analysis.ArrayAccessAnalysisAbstractValue.{Interval, Unknown}
import be.unamur.info.infom227.small.ast.*
import be.unamur.info.infom227.small.cfg.Cfg

enum ArrayAccessAnalysisAbstractValue extends Lattice[ArrayAccessAnalysisAbstractValue]:
  case Unknown
  case Interval(lower: Double, upper: Double)
  case Bottom

  override def join(other: ArrayAccessAnalysisAbstractValue): ArrayAccessAnalysisAbstractValue = {
    (this, other) match {
      case (ArrayAccessAnalysisAbstractValue.Bottom, _) => other
      case (_, ArrayAccessAnalysisAbstractValue.Bottom) => this
      case (ArrayAccessAnalysisAbstractValue.Interval(a, b), ArrayAccessAnalysisAbstractValue.Interval(c, d)) =>
        val lo = math.min(a, c)
        val hi = math.max(b, d)
        if (lo > hi) ArrayAccessAnalysisAbstractValue.Bottom
        else ArrayAccessAnalysisAbstractValue.Interval(lo, hi)
      case _ => ArrayAccessAnalysisAbstractValue.Unknown
    }
  }

  override def meet(other: ArrayAccessAnalysisAbstractValue): ArrayAccessAnalysisAbstractValue = {
    (this, other) match {
      case (ArrayAccessAnalysisAbstractValue.Unknown, _) => other
      case (_, ArrayAccessAnalysisAbstractValue.Unknown) => this
      case (ArrayAccessAnalysisAbstractValue.Interval(a, b), ArrayAccessAnalysisAbstractValue.Interval(c, d)) =>
        val lo = math.max(a, c)
        val hi = math.min(b, d)
        if (lo > hi) ArrayAccessAnalysisAbstractValue.Bottom
        else ArrayAccessAnalysisAbstractValue.Interval(lo, hi)
      case _ => ArrayAccessAnalysisAbstractValue.Bottom
    }
  }

  override def toString: String = {
    this match {
      case ArrayAccessAnalysisAbstractValue.Unknown => "U"
      case ArrayAccessAnalysisAbstractValue.Bottom => "⊥"
      case ArrayAccessAnalysisAbstractValue.Interval(a, b) => s"[$a, $b]"
    }
  }

class ArrayAccessAnalysis(cfg: Cfg) extends ForwardMayAnalyzer[AbstractState[ArrayAccessAnalysisAbstractValue]](cfg):
  override def entryAbstractState(): AbstractState[ArrayAccessAnalysisAbstractValue] = AbstractState(cfg.parameters.map { parameter => parameter -> ArrayAccessAnalysisAbstractValue.Unknown }.toMap)

  final override def analyseStatement(abstractState: AbstractState[ArrayAccessAnalysisAbstractValue], statement: Statement): AbstractState[ArrayAccessAnalysisAbstractValue] = {
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
          case _ =>
            abstractState(variable -> Unknown)
        }
      case _ =>
        abstractState
    }
  }

  final override def conditionUpdate(abstractState: AbstractState[ArrayAccessAnalysisAbstractValue], condition: BooleanExpression): Option[AbstractState[ArrayAccessAnalysisAbstractValue]] = {
    condition match {
      case IntegerComparisonOperation(Variable(v), IntegerComparisonOperator.Lt, ArithmeticConstant(c)) =>
        abstractState(v).meet(Interval(Double.NegativeInfinity, c.toDouble - 1)) match {
          case ArrayAccessAnalysisAbstractValue.Bottom => None
          case refined => Some(abstractState(v -> refined))
        }
      case IntegerComparisonOperation(Variable(v), IntegerComparisonOperator.Gte, ArithmeticConstant(c)) =>
        abstractState(v).meet(Interval(c.toDouble, Double.PositiveInfinity)) match {
          case ArrayAccessAnalysisAbstractValue.Bottom => None
          case refined => Some(abstractState(v -> refined))
        }
      case _ =>
        Some(abstractState)
    }
  }
