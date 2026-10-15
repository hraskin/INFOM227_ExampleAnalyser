package be.unamur.info.infom227.small.interpreter

import be.unamur.info.infom227.small.ast.*

import scala.collection.immutable.HashMap
import scala.util.{Failure, Success, Try}

final case class ArrayValue(elements: List[VariableType])

type VariableType = Int | Boolean | ArrayValue

def execute(program: Program, entry: String, arguments: List[VariableType] = List.empty): Try[VariableType] = {
  program.functions.get(entry) match {
    case Some(entryFunction) =>
      if (entryFunction.parameters.length != arguments.length) {
        Failure(RuntimeException(s"The number of arguments (${arguments.length}) does not match the number of parameters (${entryFunction.parameters.length})."))
      } else {
        for {
          (_, returnValue) <- executeFunction(program, Environments().push(entryFunction.parameters.zip(arguments).toMap), entryFunction.body)
        } yield returnValue
      }
    case None =>
      Failure(RuntimeException("No entry function found in the program."))
  }
}

def executeFunction(
  program: Program,
  environments: Environments[VariableType],
  body: List[Statement]
): Try[(Environments[VariableType], VariableType)] = {
  for {
    (newEnvironments, returnValueOption) <- executeSequence(program, environments, body)
    updatedEnvironments <- newEnvironments.pop()
    returnValue <- returnValueOption match {
      case Some(value) => Success(value)
      case None => Failure(RuntimeException("Function did not return a value."))
    }
  } yield (updatedEnvironments, returnValue)
}

def executeSequence(
  program: Program,
  environments: Environments[VariableType],
  sequence: List[Statement]
): Try[(Environments[VariableType], Option[VariableType])] = {
  sequence match {
    case Nil => Success((environments, None))
    case statement :: rest =>
      for {
        (newEnvironments, returnValueOption) <- executeStatement(program, environments, statement)
        result <- returnValueOption match {
          case Some(returnValue) => Success((newEnvironments, Some(returnValue)))
          case None => executeSequence(program, newEnvironments, rest)
        }
      } yield result
  }
}

def executeStatement(
  program: Program,
  environments: Environments[VariableType],
  statement: Statement
): Try[(Environments[VariableType], Option[VariableType])] = {
  statement match {
    case assignStatement: AssignStatement => executeAssignStatement(program, environments, assignStatement)
    case arrayAssignStatement: ArrayAssignStatement => executeArrayAssignStatement(program, environments, arrayAssignStatement)
    case ifStatement: IfStatement => executeIfStatement(program, environments, ifStatement)
    case whileStatement: WhileStatement => executeWhileStatement(program, environments, whileStatement)
    case returnStatement: ReturnStatement => executeReturnStatement(program, environments, returnStatement)
  }
}

def executeAssignStatement(
  program: Program,
  environments: Environments[VariableType],
  assignStatement: AssignStatement
): Try[(Environments[VariableType], Option[VariableType])] = {
  assignStatement.expression match {
    case expression: Expression => for {
      value <- executeExpression(environments, expression)
      newEnvironments <- environments.updated(assignStatement.variable, value)
    } yield (newEnvironments, None)
    case call: FunctionCall =>
      for {
        (newEnvironments, returnValue) <- executeCall(program, environments, call)
        updatedEnvironments <- environments.updated(assignStatement.variable, returnValue)
      } yield (updatedEnvironments, None)
    case arrayLit: ArrayLit =>
      for {
        arrayValue <- executeArrayLit(environments, arrayLit)
        updatedEnvironments <- environments.updated(assignStatement.variable, arrayValue)
      } yield (updatedEnvironments, None)
  }
}

def executeIfStatement(
  program: Program,
  environments: Environments[VariableType],
  ifStatement: IfStatement
): Try[(Environments[VariableType], Option[VariableType])] = {
  for {
    conditionValue <- executeBooleanExpression(environments, ifStatement.condition)
    result <- if (conditionValue) {
      executeSequence(program, environments, ifStatement.ifBody)
    } else {
      executeSequence(program, environments, ifStatement.elseBody)
    }
  } yield result
}

def executeArrayAssignStatement(program: Program, environments: Environments[VariableType], arrayAssignStatement: ArrayAssignStatement): Try[(Environments[VariableType], Option[VariableType])] = {
  def store(envs: Environments[VariableType], index: Int, value: VariableType): Try[Environments[VariableType]] =
    for {
      array <- envs.get(arrayAssignStatement.variable)
      updated <- array match {
        case ArrayValue(elements) => Try(elements.updated(index, value))
        case _ => Failure(RuntimeException(s"Variable '${arrayAssignStatement.variable}' is not an array."))
      }
      result <- envs.updated(arrayAssignStatement.variable, ArrayValue(updated))
    } yield result

  for {
    index <- executeArithmeticExpression(environments, arrayAssignStatement.index)
    updatedEnvironments <- arrayAssignStatement.expression match {
      case expression: Expression =>
        executeExpression(environments, expression).flatMap(store(environments, index, _))
      case call: FunctionCall =>
        executeCall(program, environments, call).flatMap { case (newEnvs, returnValue) =>
          store(newEnvs, index, returnValue)
        }
    }
  } yield (updatedEnvironments, None)
}

def executeArrayLit(environments: Environments[VariableType], arrayLit: ArrayLit): Try[ArrayValue] = {
  arrayLit.elems.foldLeft(Success(List.empty[VariableType]): Try[List[VariableType]]) { (acc, e) =>
    for {xs <- acc; v <- executeExpression(environments, e)} yield xs :+ v
  }.map(ArrayValue(_))
}

def executeWhileStatement(
  program: Program,
  environments: Environments[VariableType],
  whileStatement: WhileStatement
): Try[(Environments[VariableType], Option[VariableType])] = {
  for {
    conditionValue <- executeBooleanExpression(environments, whileStatement.condition)
    result <- if (conditionValue) {
      for {
        (newEnvironments, returnValueOption) <- executeSequence(program, environments, whileStatement.body)
        finalResult <- returnValueOption match {
          case Some(returnValue) => Success((newEnvironments, Some(returnValue)))
          case None => executeWhileStatement(program, newEnvironments, whileStatement)
        }
      } yield finalResult
    } else {
      Success((environments, None))
    }
  } yield result
}

def executeReturnStatement(
  program: Program,
  environments: Environments[VariableType],
  returnStatement: ReturnStatement
): Try[(Environments[VariableType], Option[VariableType])] = {
  for {
    returnValue <- executeExpression(environments, returnStatement.expression)
  } yield (environments, Some(returnValue))
}

def executeExpression(environments: Environments[VariableType], expression: Expression): Try[VariableType] = {
  expression match {
    case variable: Variable => environments.get(variable.name)
    case arithmeticExpression: ArithmeticExpression => executeArithmeticExpression(environments, arithmeticExpression)
    case booleanExpression: BooleanExpression => executeBooleanExpression(environments, booleanExpression)
  }
}

def executeArithmeticExpression(
  environments: Environments[VariableType],
  arithmeticExpression: ArithmeticExpression
): Try[Int] = {
  arithmeticExpression match {
    case ArithmeticConstant(value) => Success(value)
    case ArithmeticBinaryOperation(left, operator, right) =>
      for {
        leftValue <- executeArithmeticExpression(environments, left)
        rightValue <- executeArithmeticExpression(environments, right)
        result <- operator match {
          case ArithmeticBinaryOperator.Add => Success(leftValue + rightValue)
          case ArithmeticBinaryOperator.Sub => Success(leftValue - rightValue)
          case ArithmeticBinaryOperator.Mul => Success(leftValue * rightValue)
          case ArithmeticBinaryOperator.Div =>
            if (rightValue == 0) {
              Failure(RuntimeException("Division by zero."))
            } else {
              Success(leftValue / rightValue)
            }
        }
      } yield result
    case Variable(name) =>
      for {
        value <- environments.get(name)
        intValue <- value match {
          case intValue: Int => Success(intValue)
          case _ => Failure(RuntimeException(s"Variable '$name' is not an integer."))
        }
      } yield intValue
    case ArrayAccess(variable, index) =>
      executeArrayAccess(environments, ArrayAccess(variable, index)).flatMap {
        case intValue: Int => Success(intValue)
        case _ => Failure(RuntimeException(s"Element at index $index of array '${variable.name}' is not an integer."))
      }
  }
}

def executeBooleanExpression(
  environments: Environments[VariableType],
  booleanExpression: BooleanExpression
): Try[Boolean] = {
  booleanExpression match {
    case BooleanConstant(value) => Success(value)
    case BooleanNegOperation(value) =>
      for {
        boolValue <- executeBooleanExpression(environments, value)
      } yield !boolValue
    case BooleanBinaryOperation(left, operator, right) =>
      for {
        leftValue <- executeBooleanExpression(environments, left)
        rightValue <- executeBooleanExpression(environments, right)
        result <- operator match {
          case BooleanBinaryOperator.And => Success(leftValue && rightValue)
          case BooleanBinaryOperator.Or => Success(leftValue || rightValue)
          case EqualComparisonOperator.Eq => Success(leftValue == rightValue)
          case EqualComparisonOperator.Ne => Success(leftValue != rightValue)
        }
      } yield result
    case IntegerComparisonOperation(left, operator, right) =>
      for {
        leftValue <- executeArithmeticExpression(environments, left)
        rightValue <- executeArithmeticExpression(environments, right)
        result <- operator match {
          case IntegerComparisonOperator.Gt => Success(leftValue > rightValue)
          case IntegerComparisonOperator.Lt => Success(leftValue < rightValue)
          case EqualComparisonOperator.Eq => Success(leftValue == rightValue)
          case EqualComparisonOperator.Ne => Success(leftValue != rightValue)
          case IntegerComparisonOperator.Gte => Success(leftValue >= rightValue)
          case IntegerComparisonOperator.Lte => Success(leftValue <= rightValue)
        }
      } yield result
    case Variable(name) =>
      for {
        value <- environments.get(name)
        boolValue <- value match {
          case boolValue: Boolean => Success(boolValue)
          case _ => Failure(RuntimeException(s"Variable '$name' is not a boolean."))
        }
      } yield boolValue
    case ArrayAccess(variable, index) =>
      executeArrayAccess(environments, ArrayAccess(variable, index)).flatMap {
        case boolValue: Boolean => Success(boolValue)
        case _ => Failure(RuntimeException(s"Element at index $index of array '${variable.name}' is not a boolean."))
      }
  }
}

def executeArrayAccess(environments: Environments[VariableType], arrayAccess: ArrayAccess): Try[VariableType] = {
  for {
    arrayValue <- environments.get(arrayAccess.variable.name)
    index <- executeArithmeticExpression(environments, arrayAccess.index)
    element <- arrayValue match {
      case ArrayValue(xs) => Success(xs(index))
      case _ => Failure(RuntimeException(s"'${arrayAccess.variable.name}' is not an array."))
    }
  } yield element
}

def executeCall(
  program: Program,
  environments: Environments[VariableType],
  call: FunctionCall
): Try[(Environments[VariableType], VariableType)] = {
  program.functions.get(call.name) match {
    case Some(function) =>
      for {
        arguments <- call.arguments.foldLeft(Success(List.empty[VariableType]): Try[List[VariableType]]) { (acc, arg) =>
          for {
            args <- acc
            value <- executeExpression(environments, arg)
          } yield args :+ value
        }
        _ <- if (function.parameters.length != arguments.length) {
          Failure(RuntimeException(s"Function '${call.name}' expects ${function.parameters.length} arguments, but got ${arguments.length}."))
        } else {
          Success(())
        }
        functionEnvironment = environments.push(HashMap(function.parameters.zip(arguments) *))
        result <- executeFunction(program, functionEnvironment, function.body)
      } yield result
    case None =>
      Failure(RuntimeException(s"Function '${call.name}' not found."))
  }
}
