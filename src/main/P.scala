import ExprOp.ExprOp
import TupleOps.flatten

import scala.io.Source
import scala.language.{implicitConversions, postfixOps}
import scala.util.Using
import StringOps.*
import TermOp.TermOp

// ========================================================================================
trait P[+A]:
  // ======================================================================================
  def apply(input: List[Token]): ParseResult[A]
  def apply(input: String): ParseResult[A] = apply(input.listed)
  // ======================================================================================
  /** compose this parser with another, passing the captured type A along */
  def flatMap[B](f: A => P[B]): P[B] =
    (input: List[Token]) => apply(input) match
      case Success(a, ts) => f(a)(ts)
      case f: Failure => f

  def ||> [B](f: A => P[B]): P[B] = flatMap(f)
  // ======================================================================================
  /** transform the internal captured type from A to B */
  def map[B](f: A => B): P[B] =
    (input: List[Token]) => apply(input) match
      case Success(a, ts) => Success(f(a), ts)
      case f: Failure => f
  // ======================================================================================
  /** (map) transform the internal captured type from A to B */
  def |> [B](f: A => B): P[B] = map(f)
  // ======================================================================================
  /** (and) accept A followed by B, capturing both as a tuple, fail otherwise */
  def & [B](pb: P[B]): P[(A, B)] =
    (input: List[Token]) => apply(input) match
      case Success(a, t1) => pb(t1) match
        case Success(b, t2) => Success((a, b), t2)
        case f: Failure => f
      case f: Failure => f
  /** (and left) accept A followed by B, capturing only the left hand side, fail otherwise */
  def <& [B](pb: P[B]): P[A] =
    (this & pb) |> { case (a, b) => a }
  // ======================================================================================
  /** (and right) accept A followed by B, capturing only the right hand side, fail otherwise */
  def &> [B](pb: P[B]): P[B] =
    (this & pb) |> { case (a, b) => b }
  // ======================================================================================
  /** (or) accept A or B, capturing whichever is found first, fail otherwise */
//  def | [B](pb: P[B]): P[A | B] =
//    (input: List[Token]) => apply(input) match
//      case s1: Success[_] => s1
//      case f1: Failure => pb(input) match
//        case s2: Success[_] => s2
//        case f2: Failure =>
//          Failure(s"${f1.message}\n${f2.message}", input)
  def | [B >: A](pb: P[B]): P[B] =
    (input: List[Token]) => apply(input) match
      case s1: Success[A] => s1
      case f1: Failure => pb(input) match
        case s2: Success[B] => s2
        case f2: Failure =>
          Failure(s"${f1.message}\n${f2.message}", input)
  // ======================================================================================
  /** collect all matches, returning when no more matches, always returns Success */
  private def recurse(input: List[Token]): (List[A], List[Token]) =
    this.apply(input) match
      case _: Failure => (List.empty, input)
      case Success(a1, t1) =>
        val (a2, t2) = recurse(t1)
        (a1::a2, t2)
  // ======================================================================================
  /** collect matches up to a limit, returns if no more matches, always return Success */
  private def bounded_recurse(input: List[Token])(depth: Int)
    : (List[A], List[Token]) =
    if depth == 0 then (List.empty, input)
    else this.apply(input) match
      case _: Failure => (List.empty, input)
      case Success(a1, t1) =>
        val (a2, t2) = bounded_recurse(t1)(depth - 1)
        (a1::a2, t2)
  // ======================================================================================
  /** (zero or more) match 0 or many As, collected in a list, always returns Success */
  def * : P[List[A]] =
    (input: List[Token]) =>
      val(a, t) = recurse(input)
      Success(a, t)
  // ======================================================================================
  /** (one or more) match 1 or many As, collected in a list, fail if none */
  def + : P[List[A]] =
    (input: List[Token]) => apply(input) match
      case f: Failure => f
      case Success(a1, t1) =>
        val (a2, t2) = recurse(t1)
        Success(a1::a2, t2)
  // ======================================================================================
  /** (any repetitions) match up to (inclusive) n amount of As, collected in a list, always succeed */
  def #* (depth: Int) : P[List[A]] =
    (input: List[Token]) =>
      val(a, t) = bounded_recurse(input)(depth)
      Success(a, t)
  // ======================================================================================
  /** (exact repetitions) match up to n amount of As, collected in a list, fail if found is not n */
  def #= (depth: Int) : P[List[A]] =
    (input: List[Token]) =>
      val(a, t) = bounded_recurse(input)(depth)
      if a.length != depth then
        Failure(s"Expected: ${depth}, but only found ${a.length}", input)
      else Success(a, t)
  // ======================================================================================
  def #+(range: (Int, Int)): P[List[A]] =
    (input: List[Token]) =>
      val(a, t) = bounded_recurse(input)(range._2)
      if a.length < range._1 || a.length > range._2 then
        Failure(s"Expected Range: ${range}, but found ${a.length}", input)
      else Success(a, t)
  // ======================================================================================
  def ! (msg: String) : P[A] =
    (input: List[Token]) => apply(input) match
      case Failure(_, t) => Failure(msg, t)
      case s: Success[A] => s
end P
// ========================================================================================



object P
{
  extension [A, B] (pf: P[A => B])
    def use(pa: P[A]): P[B] =
      (pf & pa).map { case (f, b) => f(b) }

  def apply[A, T >: Token](f: List[T] => ParseResult[A]): P[A] =
    (input: List[Token]) => f(input)
  def pure[A](value: A): P[A] =
    (input: List[Token]) => Success(value, input)

  def lift[A, B, C](f: A => B => C)(pa: P[A])(pb: P[B]): P[C] =
    pure(f).use(pa).use(pb)

  private def seq[A](ps: List[P[A]]): P[List[A]] = {
    def append(pa: A)(pas: List[A]): List[A] = pa :: pas
    val appendParser = lift(append)
    ps match
      case (h::t) => appendParser(h)(seq(t))
      case _ => pure(List.empty[A])
  }

  def sequence[A](ps: P[A]*): P[List[A]] = seq(ps.toList)

  def ? [A](pa: P[A]): P[Option[A]] =
    val some: P[Option[A]] = pa |> { a => Some(a) }
    val none: P[Option[A]] = pure(None)
    some | none


  def chr(target: String): P[String] =
    (input: List[String]) =>
      input match
        case s::ss => s.listed match
          case c::cs =>
            if target equals c then
              val out = if cs.isEmpty then ss else cs.mkString::ss
              Success(s"${c}", out)
            else Failure("Fail 1", input)
          case _ => Failure("Fail 2", input)
        case _ => Failure("Fail 3", input)



  def str(target: String): P[String] =
    val ps = target.listed map (s => chr(s))
    seq(ps) |> (l => l.mkString)


  def choice[A](ps: List[P[A]]): P[A] =
    ps.reduceLeft { case (pa, a) => pa | a }

  def any(targets: List[String]): P[String] =
    choice(targets.map(t => chr(t)))


  private val LOWER = "abcdefghijklmnopqrstuvwxyz".listed
  private val UPPER = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".listed
  private val DIGIT = "0123456789".listed
  private val WHITESPACE = " \t\n".listed

  def lowercase: P[String] = any(LOWER)
  def uppercase: P[String] = any(UPPER)
  def digit: P[String] = any(DIGIT)

  def whitespace(capture: Boolean = false): P[List[String]] =
    if capture then any(WHITESPACE)*
    else (any(WHITESPACE)*) |> { l => List.empty[String] }

  def letter: P[String] = lowercase | uppercase
  def alphanumeric: P[String] = letter | digit

}


type Token = String
trait ParseResult[+A]
case class Success[A](value: A, tokens: List[Token]) extends ParseResult[A]
case class Failure(message: String, tokens: List[Token]) extends ParseResult[Nothing]


object Test extends App
{
  import P._
  import ASM._
  import TupleOps._
  import StringOps._


  val testStr = (
    "data sec { " +
      "start = 0x00 " +
      "end = start + 0xFF" +
    "}"
  ).delimited
  println((testStr))


}

object StringOps:
// This is used extensively
  extension (string: String)
    def listed: List[String] =
      string.split("").toArray.toList

    def delimited: List[String] =
      string.split(Array(' ', '\n', '\t')).toList

    def ++(msg: String): String =
      s"${string}\n${msg}"

end StringOps

object ASM
{
  import P.*

  def id: P[Identifier] = (letter & (str("_") | alphanumeric).*)
    |> { case (l: String, a: List[String]) => l::a }
    |> { l => Identifier(l.mkString) }

  def bin8: P[Constant] =
    str("0b") &> any("01".listed) #+ (1, 8)
      |> (l => Constant(l.mkString, Type.Binary))

  def bin16: P[Constant] =
    str("0b") &> any("01".listed) #+ (1, 16)
      |> (l => Constant(l.mkString, Type.Binary))

  def dec: P[Constant] =
    str("0d") &> digit #+ (1, 5) ||>
    { list => (input: List[Token]) =>
      val int = Integer.parseInt(list.mkString, 10)
      if (int > 0xFFFF) then Failure("Integer is too large", input)
      else Success(list, input)
    } |> (l => Constant(l.mkString, Type.Decimal))

  def hex4: P[Constant] =
    str("0x") &> (digit | any("ABCDEFabcdef".listed)) #+ (1, 4)
      |> (l => Constant(l.mkString, Type.Hexadecimal))


  // Expression
  def expr: P[Expr] =
    (term & (expr_operand*))
      |> { case (t, l) => Expr(t, l)}

  def expr_operand: P[ExprOperand] =
    (expr_op & term)
      |> { case (op, t) => ExprOperand(op, t) }

  def expr_op: P[ExprOp] =
    (str("+") | str("-"))
      |> { s => ExprOp(s) }

  // Term
  def term: P[Term] =
    (factor & (term_operand*))
      |> { case (f, l) => Term(f, l) }

  def term_op: P[TermOp] =
    (str("*") | str("/"))
      |> { s => TermOp(s) }

  def term_operand: P[TermOperand] =
    (term_op & factor)
      |> { case (op, f) => TermOperand(op, f) }

  // Factor (this hand rolled works but otherwise stkoverflow)
  def factor: P[Factor] = (input: List[String]) => constant(input) match
      case s1: Success[_] => s1
      case f1: Failure => id(input) match
        case s2: Success[_] => s2
        case f2: Failure => parenthetical(input) match
          case s3: Success[_] => s3
          case f3: Failure => Failure(f1.message++f2.message++f3.message, input)

  def parenthetical: P[Factor] = str("(") &> expr <& str(")")

  def constant: P[Constant] =  bin16 | bin8 | hex4 | dec

  def constDec: P[ConstDec] =
    (id & (str("=") &> expr)) |> { case (i, e) => ConstDec(i, e) }

  def dataSection: P[DataSection] =
    (str("data") &> id) & dataBlock
      |> { case (i, l) => DataSection(i, l) }

  def dataBlock: P[List[ConstDec]] =
    str("{") &> (constDec*) <& str("}")

}

enum Type:
  case Binary, Hexadecimal, Decimal

object ExprOp:
  trait ExprOp
  def apply(symbol: String): ExprOp = symbol match
    case "+" => Plus
    case "-" => Minus
  case object Plus extends ExprOp
  case object Minus extends ExprOp
end ExprOp

object TermOp:
  trait TermOp
  def apply(symbol: String): TermOp = symbol match
    case "*" => Multiply
    case "/" => Divide
  case object Multiply extends TermOp
  case object Divide extends TermOp
end TermOp


// Expression
case class Expr(arg1: Term, operand: List[ExprOperand]) extends Factor
case class ExprOperand(operator: ExprOp, arg2: Term)
case class Term(arg1: Factor, operands: List[TermOperand])
case class TermOperand(operator: TermOp, arg2: Factor)
trait Factor
case class Constant(value: String, _type: Type) extends Factor
case class Identifier(value: String) extends Factor

case class ConstDec(id: Identifier, expr: Expr)

case class DataSection(id: Identifier, consts: List[ConstDec])



import scala.annotation.targetName

object TupleOps
{
  @targetName("flt1")
  def flatten[A, B, C](t: ((A, B), C)): (A, B, C) =
    (t._1._1, t._1._2, t._2)
  @targetName("flt2")
  def flatten[A, B, C](t: (A, (B, C))): (A, B, C) =
    (t._1, t._2._1, t._2._2)
  @targetName("flt3")
  def flatten[A, B, C, D](t: ((A, B, C), D)): (A, B, C, D) =
    (t._1._1, t._1._2, t._1._3, t._2)
  @targetName("flt4")
  def flatten[A, B, C, D](t: ((A, B), (C, D))): (A, B, C, D) =
    (t._1._1, t._1._2, t._2._1, t._2._2)
  @targetName("flt5")
  def flatten[A, B, C, D](t: ((A), (B, C, D))): (A, B, C, D) =
    (t._1, t._2._1, t._2._2, t._2._3)
  @targetName("flt6")
  def flatten[A, B, C, D](t: ((A, B), C, D)): (A, B, C, D) =
    (t._1._1, t._1._2, t._2, t._3)
}


def load(): String =
  val file = "/home/bryce/Projects/cppsim/test/ex2.asm"
  val try_text = Using (Source.fromFile(file)) { r =>
    r.getLines().map(s => s"${s}\n").mkString }
  try_text.getOrElse(throw new Exception("Failed to Load"))
