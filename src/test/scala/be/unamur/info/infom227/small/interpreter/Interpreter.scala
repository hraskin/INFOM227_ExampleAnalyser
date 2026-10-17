package be.unamur.info.infom227.small.interpreter

import be.unamur.info.infom227.small.{ast, cst, interpreter}
import org.antlr.v4.runtime.CharStreams
import org.scalatest.funsuite.AnyFunSuite

import scala.util.{Failure, Success}

class Interpreter extends AnyFunSuite {
  Seq(
    (
      "execute an addition operation",
      """
      function main() {
          a = 3 + 2;
          return a;
      }
      """,
      5
    ),
    (
      "execute a subtraction operation",
      """
      function main() {
          a = 3 - 2;
          return a;
      }
      """,
      1
    ),
    (
      "execute a multiple operation",
      """
      function main() {
          a = 6 * 2;
          return a;
      }
      """,
      12
    ),
    (
      "execute a division operation",
      """
      function main() {
          a = 6 / 2;
          return a;
      }
      """,
      3
    ),
    (
      "execute a logical AND operation",
      """
      function main() {
          a = True and False;
          return a;
      }
      """,
      false
    ),
    (
      "execute a logical OR operation",
      """
      function main() {
          a = True or False;
          return a;
      }
      """,
      true
    ),
    (
      "execute a simple if statement",
      """
      function main() {
          x = True;
          if (x) {
              a = 4;
          } else {
              a = 2;
          }
          return a;
      }
      """,
      4
    ),
    (
      "execute a simple while statement",
      """
      function main() {
          i = 1;
          while (i < 5) {
              i = i * 2;
          }
          return i;
      }
      """,
      8
    ),
    (
      "execute a simple function call",
      """
      function foo(a) {
          return a + 1;
      }
      function main() {
          i = 1;
          x = foo(i);
          return x;
      }
      """,
      2
    ),
    (
      "execute a shadowing function call",
      """
      function foo(a) {
          i = 5;
          return i + 1;
      }
      function main() {
          i = 1;
          x = foo(i);
          return x;
      }
      """,
      6
    ),
    (
      "execute an unused shadowing function call",
      """
      function foo(a) {
          i = 5;
          return i + 1;
      }
      function main() {
          i = 1;
          x = foo(i);
          return i;
      }
      """,
      1
    ),
    (
      "execute the fibonacci function",
      """
      function fib(x) {
          if (x <= 1) {
              return x;
          } else {
              minus1 = fib(x - 1);
              minus2 = fib(x - 2);
              return minus1 + minus2;
          }
      }
      function main() {
          x = fib(15);
          return x;
      }
      """,
      610
    ),
    (
      "execute the power function (Syllabus - Chapter 2)",
      """
      function power(x, n) {
          r = 1;
          while (n > 0) {
              r = r * x;
              n = n - 1;
          }
          return r;
      }

      function main() {
          result = power(2, 3);
          return result;
      }
      """,
      8
    ),
    (
      "execute array sum",
      """
      function main() {
          a = {1, 2, 3};
          i = 0;
          total = 0;

          while (i < 3) {
              total = total + a[i];
              i = i + 1;
          }
          return total;
      }
      """,
      6
    ),
    (
      "execute expression with array access",
      """
      function main() {
          a = {1, 2, 3};
          b = a[0] + a[1];
          b = b + a[2];
          return b;
      }
      """,
      6
    ),
    (
      "execute expression with boolean array access",
      """
      function main() {
          a = {True, False, True};
          b = a[0] and a[1];
          b = b or a[2];
          return b;
      }
      """,
      true
    ),
    (
      "execute array assignment and access",
      """
      function main() {
          a = {1, 2, 3};
          a[1] = 5;
          return a[1];
      }
      """,
      5
    ),
    (
      "execute multiple array assignments",
      """
      function main() {
          a = {1, 2, 3};
          b = {4, 5, 6};

          a[0] = b[0];
          a[1] = b[1];
          a[2] = b[2];

          return a[0] + a[1];
      }
      """,
      9
    )
  ).foreach { (name, code, expected) =>
    test(name) {
      val charStream = CharStreams.fromString(code)

      val result = for {
        programContext <- cst.parse(charStream)
        program <- ast.build(programContext)
        result <- interpreter.execute(program, "main")
      } yield result

      assert(Success(expected) == result)
    }
  }

  test("reject assigning an array to an array element") {
    val code =
      """
      function main() {
          a = {1, 2};
          b = {3, 4};
          a[0] = b;
          return 0;
      }
      """
    val charStream = CharStreams.fromString(code)

    val result = for {
      programContext <- cst.parse(charStream)
      program <- ast.build(programContext)
      result <- interpreter.execute(program, "main")
    } yield result

    assert(result.failed.get.getMessage == "Cannot assign an array to an array element.")
    assert(result.isFailure)
  }
}
