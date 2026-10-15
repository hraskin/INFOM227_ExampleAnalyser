package be.unamur.info.infom227.small.ast

import be.unamur.info.infom227.small.ast.*
import be.unamur.info.infom227.small.{ast, cst}
import org.antlr.v4.runtime.CharStreams
import org.scalatest.funsuite.AnyFunSuite

import scala.util.Success

class TestAstBuilder extends AnyFunSuite {
  Seq(
    (
      "build AST with math operations",
      """
      function main() {
          a = 3 * 4;
          a = a / 5;
          b = 7 - a;
          x = 10 + 2;
          return 0;
      }
      """,
      Program(
        Map(
          "main" -> Function(
            2,
            List.empty,
            List(
              AssignStatement(
                3,
                "a",
                ArithmeticBinaryOperation(
                  ArithmeticConstant(3),
                  ArithmeticBinaryOperator.Mul,
                  ArithmeticConstant(4)
                )
              ),
              AssignStatement(
                4,
                "a",
                ArithmeticBinaryOperation(
                  Variable("a"),
                  ArithmeticBinaryOperator.Div,
                  ArithmeticConstant(5)
                )
              ),
              AssignStatement(
                5,
                "b",
                ArithmeticBinaryOperation(
                  ArithmeticConstant(7),
                  ArithmeticBinaryOperator.Sub,
                  Variable("a")
                )
              ),
              AssignStatement(
                6,
                "x",
                ArithmeticBinaryOperation(
                  ArithmeticConstant(10),
                  ArithmeticBinaryOperator.Add,
                  ArithmeticConstant(2)
                )
              ),
              ReturnStatement(7, ArithmeticConstant(0))
            )
          )
        )
      )
    ),
    (
      "build AST with boolean operations",
      """
      function main() {
          a = True and False;
          a = a or True;
          b = 4 == 5;
          c = 4 != 5;
          d = 4 < 5;
          e = 4 <= 5;
          f = 4 > 5;
          g = 4 >= 5;
          return 0;
      }
      """,
      Program(
        Map(
          "main" -> Function(
            2,
            List.empty,
            List(
              AssignStatement(
                3,
                "a",
                BooleanBinaryOperation(
                  BooleanConstant(true),
                  BooleanBinaryOperator.And,
                  BooleanConstant(false)
                )
              ),
              AssignStatement(
                4,
                "a",
                BooleanBinaryOperation(
                  Variable("a"),
                  BooleanBinaryOperator.Or,
                  BooleanConstant(true)
                )
              ),
              AssignStatement(
                5,
                "b",
                IntegerComparisonOperation(
                  ArithmeticConstant(4),
                  EqualComparisonOperator.Eq,
                  ArithmeticConstant(5)
                )
              ),
              AssignStatement(
                6,
                "c",
                IntegerComparisonOperation(
                  ArithmeticConstant(4),
                  EqualComparisonOperator.Ne,
                  ArithmeticConstant(5)
                )
              ),
              AssignStatement(
                7,
                "d",
                IntegerComparisonOperation(
                  ArithmeticConstant(4),
                  IntegerComparisonOperator.Lt,
                  ArithmeticConstant(5)
                )
              ),
              AssignStatement(
                8,
                "e",
                IntegerComparisonOperation(
                  ArithmeticConstant(4),
                  IntegerComparisonOperator.Lte,
                  ArithmeticConstant(5)
                )
              ),
              AssignStatement(
                9,
                "f",
                IntegerComparisonOperation(
                  ArithmeticConstant(4),
                  IntegerComparisonOperator.Gt,
                  ArithmeticConstant(5)
                )
              ),
              AssignStatement(
                10,
                "g",
                IntegerComparisonOperation(
                  ArithmeticConstant(4),
                  IntegerComparisonOperator.Gte,
                  ArithmeticConstant(5)
                )
              ),
              ReturnStatement(11, ArithmeticConstant(0))
            )
          )
        )
      )
    ),
    (
      "build AST with if statement",
      """
      function main() {
          x = 5;
          if (x > 0) {
              x = x - 1;
          } else {
              x = x + 1;
          }
          return 0;
      }
      """,
      Program(
        Map(
          "main" -> Function(
            2,
            List.empty,
            List(
              AssignStatement(
                3,
                "x",
                ArithmeticConstant(5)
              ),
              IfStatement(
                4,
                IntegerComparisonOperation(
                  Variable("x"),
                  IntegerComparisonOperator.Gt,
                  ArithmeticConstant(0)
                ),
                List(
                  AssignStatement(
                    5,
                    "x",
                    ArithmeticBinaryOperation(
                      Variable("x"),
                      ArithmeticBinaryOperator.Sub,
                      ArithmeticConstant(1)
                    )
                  )
                ),
                List(
                  AssignStatement(
                    7,
                    "x",
                    ArithmeticBinaryOperation(
                      Variable("x"),
                      ArithmeticBinaryOperator.Add,
                      ArithmeticConstant(1)
                    )
                  )
                )
              ),
              ReturnStatement(9, ArithmeticConstant(0))
            )
          )
        )
      )
    ),
    (
      "build AST with while statement",
      """
      function main() {
          x = 5;
          if (x > 0) {
              x = x - 1;
          } else {
              x = x + 1;
          }
          return 0;
      }
      """,
      Program(
        Map(
          "main" -> Function(
            2,
            List.empty,
            List(
              AssignStatement(
                3,
                "x",
                ArithmeticConstant(5)
              ),
              IfStatement(
                4,
                IntegerComparisonOperation(
                  Variable("x"),
                  IntegerComparisonOperator.Gt,
                  ArithmeticConstant(0)
                ),
                List(
                  AssignStatement(
                    5,
                    "x",
                    ArithmeticBinaryOperation(
                      Variable("x"),
                      ArithmeticBinaryOperator.Sub,
                      ArithmeticConstant(1)
                    )
                  )
                ),
                List(
                  AssignStatement(
                    7,
                    "x",
                    ArithmeticBinaryOperation(
                      Variable("x"),
                      ArithmeticBinaryOperator.Add,
                      ArithmeticConstant(1)
                    )
                  )
                )
              ),
              ReturnStatement(9, ArithmeticConstant(0))
            )
          )
        )
      )
    ),
    (
      "build AST with array assignments",
      """
      function main() {
          a = {1, 2, 3};
          return a[1];
      }
      """,
      Program(
        Map(
          "main" -> Function(
            2,
            List.empty,
            List(
              AssignStatement(
                3,
                "a",
                ArrayLit(List(ArithmeticConstant(1), ArithmeticConstant(2), ArithmeticConstant(3)))
              ),
              ReturnStatement(
                4,
                ArrayAccess(Variable("a"), ArithmeticConstant(1))
              )
            )
          )
        )
      )
    ),
    (
      "build AST with array access and assignment",
      """
      function main() {
          a = {1, 2, 3};
          a[1] = 5;
          return a[1];
      }
      """,
      Program(
        Map(
          "main" -> Function(
            2,
            List.empty,
            List(
              AssignStatement(
                3,
                "a",
                ArrayLit(List(ArithmeticConstant(1), ArithmeticConstant(2), ArithmeticConstant(3)))
              ),
              ArrayAssignStatement(
                4,
                "a",
                ArithmeticConstant(1),
                ArithmeticConstant(5)
              ),
              ReturnStatement(
                5,
                ArrayAccess(Variable("a"), ArithmeticConstant(1))
              )
            )
          )
        )
      )
    ),
    (
      "build AST with empty array",
      """
      function main() {
          a = {};
          return 0;
      }
      """,
      Program(
        Map(
          "main" -> Function(
            2,
            List.empty,
            List(
              AssignStatement(
                3,
                "a",
                ArrayLit(List.empty)
              ),
              ReturnStatement(4, ArithmeticConstant(0))
            )
          )
        )
      )
    ),
    (
      "build AST with array access in expression",
      """
      function main() {
          a = {1, 2, 3};
          b = a[1] + 5;
          return b;
      }
      """,
      Program(
        Map(
          "main" -> Function(
            2,
            List.empty,
            List(
              AssignStatement(
                3,
                "a",
                ArrayLit(List(ArithmeticConstant(1), ArithmeticConstant(2), ArithmeticConstant(3)))
              ),
              AssignStatement(
                4,
                "b",
                ArithmeticBinaryOperation(
                  ArrayAccess(Variable("a"), ArithmeticConstant(1)),
                  ArithmeticBinaryOperator.Add,
                  ArithmeticConstant(5)
                )
              ),
              ReturnStatement(5, Variable("b"))
            )
          )
        )
      )
    ),
    (
      "build AST with function call",
      """
      function foo(a) {
          return a + 1;
      }

      function main() {
          x = foo(5);
          return 0;
      }
      """,
      Program(
        Map(
          "foo" -> Function(
            2,
            List("a"),
            List(
              ReturnStatement(
                3,
                ArithmeticBinaryOperation(
                  Variable("a"),
                  ArithmeticBinaryOperator.Add,
                  ArithmeticConstant(1)
                )
              )
            )
          ),
          "main" -> Function(
            6,
            List.empty,
            List(
              AssignStatement(
                7,
                "x",
                FunctionCall(
                  "foo",
                  List(ArithmeticConstant(5))
                )
              ),
              ReturnStatement(8, ArithmeticConstant(0))
            )
          )
        )
      )
    )
  ).foreach { (name, code, expectedAst) =>
    test(name) {
      val charStream = CharStreams.fromString(code)

      val actualAst = for {
        actualCst <- cst.parse(charStream)
        actualAst <- ast.build(actualCst)
      } yield actualAst

      assert(Success(expectedAst) == actualAst)
    }
  }

  test("build AST with multiple function with same name") {
    val code =
      """
    function main(a) {
        return a + 1;
    }

    function main() {
        x = foo(5);
        return 0;
    }
    """

    val charStream = CharStreams.fromString(code)

    val actualAst = for {
      actualCst <- cst.parse(charStream)
      actualAst <- ast.build(actualCst)
    } yield actualAst

    assert(actualAst.isFailure)
  }
}
