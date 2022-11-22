/* --------------------------------------------------------------------------------------- *
 * --------------------------------------------------------------------------------------- *
 *                            EPL ASSIGNMENT 3 - VERSION 1.1                               *
 * --------------------------------------------------------------------------------------- *
 * --------------------------------------------------------------------------------------- */
package Assignment3.RabbitStandalone
import Assignment3.RabbitParser.RabbitParser
import Assignment3.RabbitSyntax.Syntax._

import scala.collection.immutable.ListMap

import java.io.{FileWriter, File}

object Assignment3Standalone {

  /** ************** Exercise 2 *
    */
  def isSimpleType(ty: Type): Boolean = ty match {
    case SignalTy(_)  => false
    case FunTy(a, b)  => isSimpleType(a) && isSimpleType(b)
    case PairTy(a, b) => isSimpleType(a) && isSimpleType(b)
    case ListTy(a)    => isSimpleType(a)
    case _            => true
  }
  // ----------------------------------------------------------------
  // Typechecker
  //
  def valueTy(v: Value): Type = v match {
    case UnitV      => UnitTy
    case IntV(_)    => IntTy
    case BoolV(_)   => BoolTy
    case StringV(_) => StringTy
    case ListV(_) =>
      sys.error("Impossible case: ListTy(xs) only introduced at runtime")
    case PairV(_, _) =>
      sys.error("Impossible case: PairV is only introduced at runtime")
    case FunV(_, _, _) =>
      sys.error("Impossible case: FunV is only introduced at runtime")
    case RecV(_, _, _, _, _) =>
      sys.error("Impossible case: FunV is only introduced at runtime")
    case _ =>
      sys.error(
        "Impossible case: signal values are is only introduced at runtime"
      )
  }
  // typing: calculate the return type of e, or throw an error
  def tyOf(ctx: Env[Type], e: Expr): Type = {
    e match {
      // Values
      case v: Value => valueTy(v)
      // BEGIN ANSWER
      case Var(x: Variable) => {
        ctx(x)
      }
      case Plus(e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == tyOf(ctx, e2))
        assert(tyOf(ctx, e1) == IntTy)
        IntTy
      }
      case Minus(e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == tyOf(ctx, e2))
        assert(tyOf(ctx, e1) == IntTy)
        IntTy
      }
      case Times(e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == tyOf(ctx, e2))
        assert(tyOf(ctx, e1) == IntTy)
        IntTy
      }
      case Div(e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == tyOf(ctx, e2))
        assert(tyOf(ctx, e1) == IntTy)
        IntTy
      }
      case App(e1: Expr, e2: Expr) => {
        var getTy = (
            (lt: Type) =>
              lt match {
                case FunTy(t1, t2) => (t1, t2)
                case _             => sys.error("Type Mismatch: App")
              }
        )
        var p = getTy(tyOf(ctx, e1))
        assert(p._1 == tyOf(ctx, e2))
        p._2
      }

      case Eq(e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == tyOf(ctx, e2))
        assert(tyOf(ctx, e1) == IntTy)
        BoolTy
      }
      case IfThenElse(e: Expr, e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == tyOf(ctx, e2))
        assert(tyOf(ctx, e) == BoolTy)
        tyOf(ctx, e1)
      }

      case GreaterThan(e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == tyOf(ctx, e2))
        assert(tyOf(ctx, e1) == IntTy)
        BoolTy
      }
      case LessThan(e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == tyOf(ctx, e2))
        assert(tyOf(ctx, e1) == IntTy)
        BoolTy
      }
      case Let(x: Variable, e1: Expr, e2: Expr) => {
        var t = tyOf(ctx, e1)
        var new_ctx = ctx + (x -> t)
        // -----------
        tyOf(new_ctx, e2)
      }
      case Lambda(x: Variable, ty: Type, e: Expr) => {
        // Adding things into context
        var new_ctx = ctx + (x -> ty)
        // return the type of ty -> e
        FunTy(ty, tyOf(new_ctx, e))
      }
      case Rec(f: Variable, x: Variable, tyx: Type, ty: Type, e: Expr) => {
        var new_ctx = ctx + (f -> FunTy(tyx, ty))
        new_ctx = new_ctx + (x -> tyx)
        var t2 = tyOf(new_ctx, e)
        assert(t2 == ty)
        FunTy(tyx, ty)
      }
      case Seq(e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == UnitTy)
        tyOf(ctx, e2)
      }
      case Over(e1: Expr, e2: Expr) => {
        assert(tyOf(ctx, e1) == SignalTy(FrameTy))
        var t = tyOf(ctx, e2)
        assert(t == SignalTy(FrameTy))
        t
      }
      case EmptyList(ty: Type) => {
        ListTy(ty)
      }
      case Cons(e: Expr, e2: Expr) => {
        var t = tyOf(ctx, e)
        var lt = tyOf(ctx, e2)
        assert(lt == ListTy(t))
        lt
      }
      case ListCase(e: Expr, e1: Expr, x: Variable, y: Variable, e2: Expr) => {
        // Helper function that unwraps ListTy(t)
        var getTy =
          (
              (lt: Type) =>
                lt match {
                  case ListTy(ty) => ty
                  case _          => sys.error("Type Mismatch: ListCase")
                }
          )

        var lt = tyOf(ctx, e)
        var t = getTy(lt)

        var new_ctx = ctx + (x -> t)
        new_ctx = new_ctx + (y -> lt)

        tyOf(new_ctx, e2)
      }
      case Pair(e1: Expr, e2: Expr) => {
        PairTy(tyOf(ctx, e1), tyOf(ctx, e2))
      }

      case Fst(e: Expr) => {
        var t = tyOf(ctx, e)
        var getTy =
          (
              (lt: Type) =>
                lt match {
                  case PairTy(t1, t2) => t1
                  case _              => sys.error("Type Mismatch")
                }
          )
        getTy(t)
      }
      case Snd(e: Expr) => {
        var t = tyOf(ctx, e)

        var getTy = (
            (t: Type) =>
              t match {
                case PairTy(t1, t2) => t2
                case _              => sys.error("Type Mismatch")
              }
        )
        getTy(t)
      }
      case LetFun(f: Variable, x: Variable, ty: Type, e1: Expr, e2: Expr) => {
        var new_ctx = ctx + (x -> ty)
        var t2 = tyOf(new_ctx, e1)
        new_ctx = new_ctx + (f -> FunTy(ty, t2))
        tyOf(new_ctx, e2)
      }
      case LetRec(
            f: Variable,
            x: Variable,
            xty: Type,
            ty: Type,
            e1: Expr,
            e2: Expr
          ) => {
        var new_ctx = ctx + (f -> FunTy(xty, ty))
        new_ctx = new_ctx + (x -> xty)
        assert(tyOf(new_ctx, e1) == ty)
        new_ctx = new_ctx + (f -> FunTy(xty, tyOf(new_ctx, e1)))
        tyOf(new_ctx, e2)
      }
      case LetPair(x: Variable, y: Variable, ePair: Expr, eBody: Expr) => {
        var getTy =
          (
              (t: Type) =>
                t match {
                  case PairTy(t1, t2) => (t1, t2)
                  case _              => sys.error("Type Mismatch: LetPair")
                }
          )
        var p = getTy(tyOf(ctx, ePair))
        var new_ctx = ctx + (x -> p._1)
        new_ctx = new_ctx + (y -> p._1)
        tyOf(new_ctx, eBody)
      }
      case Blank => SignalTy(FrameTy)
      case Pure(e: Expr) => {
        var t = tyOf(ctx, e)
        isSimpleType(t)
        SignalTy(t)
      }
      case Time => SignalTy(IntTy)
      case Apply(e1: Expr, e2: Expr) => {
        var getTy =
          (
              (t: Type) =>
                t match {
                  case SignalTy(FunTy(t1, t2)) => (t1, t2)
                  case _ => sys.error("Type Mismatch: Apply")
                }
          )
        var p = getTy(tyOf(ctx, e1))

        var t = tyOf(ctx, e2)
        assert(t == SignalTy(p._1))
        SignalTy(p._2)
      }
      case MoveXY(e1: Expr, e2: Expr, e3: Expr) => {
        assert(SignalTy(IntTy) == tyOf(ctx, e1))
        assert(SignalTy(IntTy) == tyOf(ctx, e2))
        assert(SignalTy(FrameTy) == tyOf(ctx, e3))

        SignalTy(FrameTy)
      }
      case When(e1: Expr, e2: Expr, e3: Expr) => {
        assert(tyOf(ctx, e1) == tyOf(ctx, e1))
        assert(tyOf(ctx, e2) == tyOf(ctx, e3))
        SignalTy(tyOf(ctx, e2))
      }
      case SignalBlock(se: Expr) => {
        SignalTy(tyOfSignal(ctx, se))
      }
      case Read(e: Expr) => {
        assert(tyOf(ctx, e) == StringTy)
        SignalTy(FrameTy)
      }
      case _ => sys.error("???" + e.toString())
      // END ANSWER
    }
  }

  /** ************** Exercise 3 *
    */

  def tyOfSignal(ctx: Env[Type], e: Expr): Type = {

    e match {
      // Values
      case v: Value          => valueTy(v)
      case SignalBlock(Time) => IntTy
      case Var(x: Variable) => {
        var t = ctx(x)
        assert(isSimpleType(t))
        t
      }
      case Plus(e1: Expr, e2: Expr) => {
        assert(tyOfSignal(ctx, e1) == tyOfSignal(ctx, e2))
        assert(tyOfSignal(ctx, e1) == IntTy)
        IntTy
      }
      case Minus(e1: Expr, e2: Expr) => {
        assert(tyOfSignal(ctx, e1) == tyOfSignal(ctx, e2))
        assert(tyOfSignal(ctx, e1) == IntTy)
        IntTy
      }
      case Times(e1: Expr, e2: Expr) => {
        assert(tyOfSignal(ctx, e1) == tyOfSignal(ctx, e2))
        assert(tyOfSignal(ctx, e1) == IntTy)
        IntTy
      }

      case Div(e1: Expr, e2: Expr) => {
        assert(tyOfSignal(ctx, e1) == tyOfSignal(ctx, e2))
        assert(tyOfSignal(ctx, e1) == IntTy)
        IntTy
      }
      case Eq(e1: Expr, e2: Expr) => {
        assert(tyOfSignal(ctx, e1) == tyOfSignal(ctx, e2))
        assert(
          (tyOfSignal(ctx, e1) == IntTy) || (tyOfSignal(ctx, e1) == BoolTy)
        )
        BoolTy
      }
      case LessThan(e1: Expr, e2: Expr) => {
        assert(tyOfSignal(ctx, e1) == tyOfSignal(ctx, e2))
        assert(tyOfSignal(ctx, e1) == IntTy)
        BoolTy
      }

      case GreaterThan(e1: Expr, e2: Expr) => {
        assert(tyOfSignal(ctx, e1) == tyOfSignal(ctx, e2))
        assert(tyOfSignal(ctx, e1) == IntTy)
        BoolTy
      }

      case IfThenElse(e1: Expr, e2: Expr, e3: Expr) => {
        var t1 = tyOfSignal(ctx, e1)
        var t2 = tyOfSignal(ctx, e2)
        var t3 = tyOfSignal(ctx, e3)
        assert(t1 == IntTy)
        assert(t2 == t3)
        t2

      }
      case App(e1: Expr, e2: Expr) => {
        var getTy =
          (
              (lt: Type) =>
                lt match {
                  case SignalTy(FunTy(t1, t2)) => (t1, t2)
                  case _             => sys.error("Type Mismatch App: " + lt.toString())
                }
          )

        var t = tyOfSignal(ctx, Escape(Pure((e1))))
        var p = getTy(t)
        assert(p._1 == tyOfSignal(ctx, e2))
        p._2

      }
      case Blank => FrameTy
      case Time  => IntTy
      case MoveXY(e1: Expr, e2: Expr, e3: Expr) => {
        var t1 = tyOfSignal(ctx, e1)
        var t2 = tyOfSignal(ctx, e2)
        var t3 = tyOfSignal(ctx, e3)
        assert(t1 == IntTy)
        assert(t2 == IntTy)
        assert(t3 == FrameTy)
        FrameTy
      }
      case When(e1: Expr, e2: Expr, e3: Expr) => {
        assert(tyOfSignal(ctx, e1) == BoolTy)
        var t2 = tyOfSignal(ctx, e2)
        var t3 = tyOfSignal(ctx, e3)
        assert(t2 == t3)
        t2
      }
      case Read(e: Expr) => {
        var t1 = tyOfSignal(ctx, e)
        assert(t1 == StringTy)
        FrameTy
      }
      case Over(e1: Expr, e2: Expr) => {
        assert(tyOfSignal(ctx, e1) == tyOfSignal(ctx, e2))
        assert(tyOfSignal(ctx, e1) == FrameTy)
        FrameTy
      }
      case Escape(e: Expr) => {
        var t = tyOf(ctx, e)
        t
      }
    }
  }

  // ----------------------------------------------------------------
  // Swapping (provided)
  def swap(e: Expr, y: Variable, z: Variable): Expr = {
    def swapVar(x: Variable, y: Variable, z: Variable): Variable =
      if (x == y) {
        z
      } else if (x == z) {
        y
      } else {
        x
      }

    def go(e: Expr): Expr = e match {
      // Values are closed
      case v: Value => v

      // Arithmetic expressions
      case Plus(t1, t2)  => Plus(go(t1), go(t2))
      case Minus(t1, t2) => Minus(go(t1), go(t2))
      case Times(t1, t2) => Times(go(t1), go(t2))
      case Div(t1, t2)   => Div(go(t1), go(t2))

      // Booleans
      case Eq(t1, t2)            => Eq(go(t1), go(t2))
      case IfThenElse(t, t1, t2) => IfThenElse(go(t), go(t1), go(t2))
      case GreaterThan(t1, t2)   => GreaterThan(go(t1), go(t2))
      case LessThan(t1, t2)      => LessThan(go(t1), go(t2))

      // Variables and let-binding
      case Var(x)         => Var(swapVar(x, y, z))
      case Let(x, t1, t2) => Let(swapVar(x, y, z), go(t1), go(t2))
      case LetFun(f, x, ty, t1, t2) =>
        LetFun(swapVar(f, y, z), swapVar(x, y, z), ty, go(t1), go(t2))
      case LetRec(f, x, xty, ty, t1, t2) =>
        LetRec(swapVar(f, y, z), swapVar(x, y, z), xty, ty, go(t1), go(t2))
      case LetPair(x1, x2, t1, t2) =>
        LetPair(swapVar(x1, y, z), swapVar(x2, y, z), go(t1), go(t2))

      // Pairs
      case Pair(t1, t2) => Pair(go(t1), go(t2))
      case Fst(t)       => Fst(go(t))
      case Snd(t)       => Snd(go(t))

      // Functions
      case Lambda(x, ty, t) => Lambda(swapVar(x, y, z), ty, go(t))
      case App(t1, t2)      => App(go(t1), go(t2))
      case Rec(f, x, xty, ty, t) =>
        Rec(swapVar(f, y, z), swapVar(x, y, z), xty, ty, go(t))

      // Lists
      case EmptyList(ty) => EmptyList(ty)
      case Cons(t1, t2)  => Cons(go(t1), go(t2))
      case ListCase(l, t1, consVar1, consVar2, t2) =>
        ListCase(
          go(l),
          go(t1),
          swapVar(consVar1, y, z),
          swapVar(consVar2, y, z),
          go(t2)
        )

      // Sequencing
      case Seq(t1, t2) => Seq(go(t1), go(t2))

      // Signals
      case Time             => Time
      case Pure(t)          => Pure(go(t))
      case Apply(t1, t2)    => Apply(go(t1), go(t2))
      case Read(t)          => Read(go(t))
      case MoveXY(x, y, a)  => MoveXY(go(x), go(y), go(a))
      case Blank            => Blank
      case Over(t1, t2)     => Over(go(t1), go(t2))
      case When(t1, t2, t3) => When(go(t1), go(t2), go(t3))
      case SignalBlock(t)   => SignalBlock(go(t))
      case Escape(t)        => Escape(go(t))

    }
    go(e)
  }

  /** ************** Exercise 4 *
    */

  // ----------------------------------------------------------------
  // Substitution e1 [e2 / x]
  def subst(e1: Expr, e2: Expr, x: Variable): Expr = {

    e1 match {
      case IntV(e)       => IntV(e)
      case BoolV(e)      => BoolV(e)
      case ListV(e)      => ListV(e)
      case StringV(e)    => StringV(e)
      case Plus(t1, t2)  => Plus(subst(t1, e2, x), subst(t2, e2, x))
      case Minus(t1, t2) => Minus(subst(t1, e2, x), subst(t2, e2, x))
      case Times(t1, t2) => Times(subst(t1, e2, x), subst(t2, e2, x))
      case Div(t1, t2)   => Div(subst(t1, e2, x), subst(t2, e2, x))
      case Eq(t1, t2)    => Eq(subst(t1, e2, x), subst(t2, e2, x))
      case GreaterThan(t1, t2) =>
        GreaterThan(subst(t1, e2, x), subst(t2, e2, x))
      case LessThan(t1, t2) => LessThan(subst(t1, e2, x), subst(t2, e2, x))
      case Lambda(y, ty, t1) => {
        val z = Gensym.gensym(y)
        val fresh_t1 = swap(t1, y, z)
        Lambda(y, ty, subst(t1, e2, x))
      }
      case Rec(f: Variable, y: Variable, tyx: Type, ty: Type, t1: Expr) => {
        // (rec f(y:τ):τ′.e0)[e/x] = rec g(z:τ):τ′.e0(y↔z)(f↔g)[e/x]
        val g = Gensym.gensym(f)
        val z = Gensym.gensym(y)
        val fresh_t1 = swap(swap(t1, y, z), f, g)
        Rec(g, z, tyx, ty, subst(fresh_t1, e2, x))
      }
      case IfThenElse(t, t1, t2) =>
        IfThenElse(subst(t, e2, x), subst(t1, e2, x), subst(t1, e2, x))
      case Var(y) =>
        if (x == y) { e2 }
        else { Var(y) }
      case Let(y, t1, t2) => {
        val z = Gensym.gensym(y);
        val fresh_t2 = swap(t2, y, z);
        Let(z, subst(t1, e2, x), subst(fresh_t2, e2, x))
      }
      case Pair(t1, t2) => Pair(subst(t1, e2, x), subst(t2, e2, x))
      case Fst(t)       => Fst(subst(t, e2, x))
      case Snd(t)       => Snd(subst(t, e2, x))
      case LetPair(x, y, t1, t2) => {
        // (let (y1, y2) = e1 in e2)[e/x] => let (z1, z2) = e1[e/x] in (e2(y1↔z1)(y2↔z2))[e/x]
        val z1 = Gensym.gensym(x)
        val z2 = Gensym.gensym(y)
        val fresh_t2 = swap(swap(t2, x, z1), y, z2)
        LetPair(z1, z2, subst(t1, e2, x), subst(fresh_t2, e2, x))
      }
      case LetFun(f: Variable, arg: Variable, ty: Type, t1: Expr, t2: Expr) => {
        // (let fun f (y:τ) = e1 in e2)[e/x] => let fun g(z:τ) = (e1(y↔z))[e/x] in (e2(f↔g))[e/x]
        val g = Gensym.gensym(f)
        val z = Gensym.gensym(arg)

        val fresh_t1 = swap(t1, arg, z)
        val fresh_t2 = swap(t2, f, g)
        LetFun(g, z, ty, subst(fresh_t1, e2, x), subst(fresh_t2, e2, x))
      }
      case LetRec(
            f: Variable,
            arg: Variable,
            xty: Type,
            ty: Type,
            t1: Expr,
            t2: Expr
          ) => {
        // (let rec f(y:τ):τ′ = e1 in e2)[e/x] => let rec g(z:τ):τ′ = (e1(f↔g)(y↔z))[e/x] in (e2(f↔g))[e/x]
        val z = Gensym.gensym(arg)
        val g = Gensym.gensym(f)
        val fresh_t1 = swap((swap(t1, f, g)), arg, z)
        val fresh_t2 = swap(t2, f, g)
        LetRec(g, z, xty, ty, subst(fresh_t1, e2, x), subst(fresh_t2, e2, x))
      }
      case EmptyList(ty) => EmptyList(ty)
      case Cons(t1, t2)  => Cons(subst(t1, e2, x), subst(t1, e2, x))
      case ListCase(t1: Expr, t2: Expr, x1: Variable, y: Variable, t3: Expr) =>
        ListCase(t1, subst(t2, e2, x), x1, y, subst(t3, e2, x))
      case UnitV => UnitV
      case Apply(t1: Expr, t2: Expr) =>
        Apply(subst(t1, e2, x), subst(t2, e2, x))
      case Read(t1: Expr)           => Read(subst(t1, e2, x))
      case Pure(t)                  => Pure(subst(t, e2, x))
      case Time                     => Time
      case Blank                    => Blank
      case Over(t1: Expr, t2: Expr) => Over(subst(t1, e2, x), subst(t2, e2, x))
      case MoveXY(t1: Expr, t2: Expr, t3: Expr) =>
        MoveXY(subst(t1, e2, x), subst(t2, e2, x), subst(t3, e2, x))
      case When(t1: Expr, t2: Expr, t3: Expr) =>
        When(subst(t1, e2, x), subst(t2, e2, x), subst(t3, e2, x))
      case SignalBlock(t1) => subst(t1, e2, x)
      // Signals

      case _ => sys.error("Wrong Substitution!!")
    }

  }

  /** ************** Exercise 5 *
    */

  // ----------------------------------------------------------------
  // Desugaring
  def desugar(e: Expr): Expr = {
    def desugarVal(v: Value): Value = v match {
      case PairV(v1, v2)          => PairV(desugarVal(v1), desugarVal(v2))
      case FunV(x, ty, e)         => FunV(x, ty, desugar(e))
      case RecV(f, x, tyx, ty, e) => RecV(f, x, tyx, ty, desugar(e))
      case ListV(vs)              => ListV(vs.map(desugarVal))
      // Signal values do not appear before evaluation happens so do not need to be desugared
      case v => v
    }
    e match {
      case v: Value => desugarVal(v)
      case LetFun(f: Variable, arg: Variable, ty: Type, e1: Expr, e2: Expr) =>
        Let(f, Lambda(arg, ty, e1), e2)
      case LetRec(
            f: Variable,
            arg: Variable,
            xty: Type,
            ty: Type,
            e1: Expr,
            e2: Expr
          ) =>
        Let(f, Rec(f, arg, xty, ty, e1), e2)
      case LetPair(x: Variable, y: Variable, e1: Expr, e2: Expr) => {
        val p = Gensym.gensym(x + " " + y)
        val t1 = Fst(Var(p))
        val t2 = Snd(Var(p))
        Let(p, e1, subst(subst(e2, t1, x), t2, y))
      }
      case Apply(e1: Expr, e2: Expr) => {
        var x = "4B33D660FED11FF6BF800293B0ADA1A8"
        Let(x, e1, e2)
      }
      case _ => sys.error("Wrong Desugaring!!!!")
      // END ANSWER
    }
  }

  /** ************** Exercise 6 *
    */
  def desugarBlock(e: Expr): Expr = {
    e match {
      case v: Value => Pure(desugar(v))
      // BEGIN ANSWER
      case SignalBlock(se) => desugarBlock(se)
      case Apply(SignalBlock(e1), SignalBlock(e2)) =>
        Apply(desugarBlock(e1), desugarBlock(e2))
      case IfThenElse(SignalBlock(e), SignalBlock(e1), SignalBlock(e2)) =>
        When(desugarBlock(e), desugarBlock(e1), desugarBlock(e2))
      case Plus(SignalBlock(e1), SignalBlock(e2)) => {
        // hexdump -vn16 -e'4/4 "%08X" 1 "\n"' /dev/urandom
        var x = "4B33D660FED11FF6BF800293B0ADA1A8"
        var y = "272F0A0C4677340CF681919024D2DAA4"
        x = Gensym.gensym(x)
        y = Gensym.gensym(y)
        Apply(
          Apply(
            Pure(Lambda(x, IntTy, Lambda(y, IntTy, Plus(Var(x), Var(y))))),
            desugarBlock(e1)
          ),
          desugarBlock(e2)
        )
      }
      case Minus(SignalBlock(e1), SignalBlock(e2)) => {
        // hexdump -vn16 -e'4/4 "%08X" 1 "\n"' /dev/urandom
        var x = "4B33D660FED11FF6BF800293B0ADA1A8"
        var y = "272F0A0C4677340CF681919024D2DAA4"
        x = Gensym.gensym(x)
        y = Gensym.gensym(y)
        Apply(
          Apply(
            Pure(Lambda(x, IntTy, Lambda(y, IntTy, Minus(Var(x), Var(y))))),
            desugarBlock(e1)
          ),
          desugarBlock(e2)
        )
      }
      case Times(SignalBlock(e1), SignalBlock(e2)) => {
        // hexdump -vn16 -e'4/4 "%08X" 1 "\n"' /dev/urandom
        var x = "4B33D660FED11FF6BF800293B0ADA1A8"
        var y = "272F0A0C4677340CF681919024D2DAA4"
        x = Gensym.gensym(x)
        y = Gensym.gensym(y)
        Apply(
          Apply(
            Pure(Lambda(x, IntTy, Lambda(y, IntTy, Times(Var(x), Var(y))))),
            desugarBlock(e1)
          ),
          desugarBlock(e2)
        )
      }
      case Div(SignalBlock(e1), SignalBlock(e2)) => {
        // hexdump -vn16 -e'4/4 "%08X" 1 "\n"' /dev/urandom
        var x = "4B33D660FED11FF6BF800293B0ADA1A8"
        var y = "272F0A0C4677340CF681919024D2DAA4"
        x = Gensym.gensym(x)
        y = Gensym.gensym(y)
        Apply(
          Apply(
            Pure(Lambda(x, IntTy, Lambda(y, IntTy, Div(Var(x), Var(y))))),
            desugarBlock(e1)
          ),
          desugarBlock(e2)
        )
      }
      case Eq(SignalBlock(e1), SignalBlock(e2)) => {
        // hexdump -vn16 -e'4/4 "%08X" 1 "\n"' /dev/urandom
        var x = "4B33D660FED11FF6BF800293B0ADA1A8"
        var y = "272F0A0C4677340CF681919024D2DAA4"
        x = Gensym.gensym(x)
        y = Gensym.gensym(y)
        Apply(
          Apply(
            Pure(Lambda(x, IntTy, Lambda(y, IntTy, Eq(Var(x), Var(y))))),
            desugarBlock(e1)
          ),
          desugarBlock(e2)
        )
      }
      case GreaterThan(SignalBlock(e1), SignalBlock(e2)) => {
        // hexdump -vn16 -e'4/4 "%08X" 1 "\n"' /dev/urandom
        var x = "4B33D660FED11FF6BF800293B0ADA1A8"
        var y = "272F0A0C4677340CF681919024D2DAA4"
        x = Gensym.gensym(x)
        y = Gensym.gensym(y)
        Apply(
          Apply(
            Pure(
              Lambda(x, IntTy, Lambda(y, IntTy, GreaterThan(Var(x), Var(y))))
            ),
            desugarBlock(e1)
          ),
          desugarBlock(e2)
        )
      }
      case LessThan(SignalBlock(e1), SignalBlock(e2)) => {
        // hexdump -vn16 -e'4/4 "%08X" 1 "\n"' /dev/urandom
        var x = "4B33D660FED11FF6BF800293B0ADA1A8"
        var y = "272F0A0C4677340CF681919024D2DAA4"
        x = Gensym.gensym(x)
        y = Gensym.gensym(y)
        Apply(
          Apply(
            Pure(Lambda(x, IntTy, Lambda(y, IntTy, LessThan(Var(x), Var(y))))),
            desugarBlock(e1)
          ),
          desugarBlock(e2)
        )
      }
      case TimeV   => TimeV
      case Read(e) => Read(desugar(e))
      case MoveXY(x, y, a) =>
        MoveXY(desugarBlock(x), desugarBlock(y), desugarBlock(a))
      case _ => sys.error("todo")
      // END ANSWER
    }
  }

  // ----------------------------------------------------------------
  // Evaluation Stage 1
  object Eval {

    /** ************** Exercise 7 *
      */

    // Some helper functions to simplify cases
    // It is also OK to analyze each case without using these helper functions
    def extractConstructor(expr: Expr): (Expr, Expr) => Expr = expr match {
      case Plus(_, _)        => Plus
      case Minus(_, _)       => Minus
      case Times(_, _)       => Times
      case Div(_, _)         => Div
      case Eq(_, _)          => Eq
      case GreaterThan(_, _) => GreaterThan
      case LessThan(_, _)    => LessThan
      case Pair(_, _)        => Pair
      case Cons(_, _)        => Cons
    }
    def extractFstArg(expr: Expr): Expr = expr match {
      case Plus(e, _)        => e
      case Minus(e, _)       => e
      case Times(e, _)       => e
      case Div(e, _)         => e
      case Eq(e, _)          => e
      case GreaterThan(e, _) => e
      case LessThan(e, _)    => e
      case Pair(e, _)        => e
      case Cons(e, _)        => e
    }
    def extractSndArg(expr: Expr): Expr = expr match {
      case Plus(_, e)        => e
      case Minus(_, e)       => e
      case Times(_, e)       => e
      case Div(_, e)         => e
      case Eq(_, e)          => e
      case GreaterThan(_, e) => e
      case LessThan(_, e)    => e
      case Pair(_, e)        => e
      case Cons(_, e)        => e
    }
    def extractOperation(expr: Expr): Value => Value => Value = expr match {
      case Plus(_, _) =>
        v1: Expr =>
          v2: Expr =>
            (v1, v2) match {
              case (IntV(v1), IntV(v2)) => IntV(v1 + v2)
            }
      case Minus(_, _) =>
        v1: Expr =>
          v2: Expr =>
            (v1, v2) match {
              case (IntV(v1), IntV(v2)) => IntV(v1 - v2)
            }
      case Times(_, _) =>
        v1: Expr =>
          v2: Expr =>
            (v1, v2) match {
              case (IntV(v1), IntV(v2)) => IntV(v1 * v2)
            }
      case Div(_, _) =>
        v1: Expr =>
          v2: Expr =>
            (v1, v2) match {
              case (IntV(v1), IntV(v2)) => IntV(v1 / v2)
            }
      case Eq(_, _) => v1: Expr => v2: Expr => BoolV(v1 == v2)
      case GreaterThan(_, _) =>
        v1: Expr =>
          v2: Expr =>
            (v1, v2) match {
              case (IntV(v1), IntV(v2)) => BoolV(v1 > v2)
            }
      case LessThan(_, _) =>
        v1: Expr =>
          v2: Expr =>
            (v1, v2) match {
              case (IntV(v1), IntV(v2)) => BoolV(v1 < v2)
            }
      case Pair(_, _) =>
        v1: Expr =>
          v2: Expr =>
            (v1, v2) match {
              case (v1: Value, v2: Value) => PairV(v1, v2) // must be values
            }
      case Cons(_, _) =>
        v1: Expr =>
          v2: Expr =>
            (v1, v2) match {
              case (v1: Value, ListV(v2)) => ListV(v1 :: v2) // must be values
            }
    }

    def eval(expr: Expr): Value = expr match {

      // Values
      case v: Value => v
      // BEGIN ANSWER
      case _ => sys.error("todo")
      // END ANSWER
    }

  }
  ////////////////////////////////////////////////////////////////////
  // ************************************************************** //
  // *            DO NOT CHANGE CODE BELOW THIS POINT             * //
  // ************************************************************** //
  ////////////////////////////////////////////////////////////////////

  // ----------------------------------------------------------------
  // Evaluation Stage 1
  object Translation {
    // import rabbitDSL._
    def paren(s: String) = "(" + s + ")"
    def brace(s: String) = "{" + s + "}"

    def tr(expr: Expr): String = expr match {
      // Arithmetic expressions
      case Plus(e1, e2)  => paren(tr(e1)) + " + " + paren(tr(e2))
      case Minus(e1, e2) => paren(tr(e1)) + " - " + paren(tr(e2))
      case Times(e1, e2) => paren(tr(e1)) + " * " + paren(tr(e2))
      case Div(e1, e2)   => paren(tr(e1)) + " / " + paren(tr(e2))

      // Booleans
      case Eq(e1, e2)          => paren(tr(e1)) + " == " + paren(tr(e2))
      case GreaterThan(e1, e2) => paren(tr(e1)) + " > " + paren(tr(e2))
      case LessThan(e1, e2)    => paren(tr(e1)) + " < " + paren(tr(e2))
      case IfThenElse(e, e1, e2) =>
        brace("if" + paren(tr(e)) + " {" + tr(e1) + "} else {" + tr(e2) + "}")

      // Variables and let-binding
      case Var(x)         => x
      case Let(x, e1, e2) => brace("val " + x + " = " + tr(e1) + "; " + tr(e2))

      // Pairs
      case Pair(e1, e2) => paren(tr(e1) + ", " + tr(e2))
      case Fst(e1)      => tr(e1) + "._1"
      case Snd(e1)      => tr(e1) + "._2"

      // Functions
      case Lambda(x, ty, e) => brace(x + ": " + trty(ty) + " => " + tr(e))
      case Rec(f, x, tyx, ty, e) =>
        paren(
          "new(" + paren(trty(tyx)) + " => " + trty(ty) + "){def apply" + paren(
            x + ": " + trty(tyx)
          ) + ": " + trty(ty) + " = " + tr(swap(e, f, "apply")) + "}"
        )
      case App(e1, e2) => paren(tr(e1)) + paren(tr(e2))

      // Lists
      case EmptyList(ty) => "Nil"
      case Cons(e1, e2)  => paren(tr(e1) + "::" + tr(e2))
      case ListCase(l, e1, x, y, e2) =>
        paren(
          tr(l) + " match " + brace(
            "case Nil => " + tr(
              e1
            ) + "; " + "case " + x + "::" + y + " => " + tr(e2)
          )
        )

      // Signals
      case Time          => "time"
      case Read(e)       => "read" + paren(tr(e))
      case Pure(e)       => "pure" + paren(tr(e))
      case Apply(e1, e2) => paren(tr(e1)) + " <*> " + paren(tr(e2))
      case MoveXY(e1, e2, e3) =>
        "moveXY" + paren(tr(e1) + ", " + tr(e2) + ", " + tr(e3))
      case When(e1, e2, e3) =>
        "when" + paren(tr(e1) + ", " + tr(e2) + ", " + tr(e3))
      case Blank        => "blank"
      case Over(e1, e2) => paren(tr(e1) + "<+>" + tr(e2))

      case TimeV          => "time"
      case ReadV(e)       => "read" + paren(tr(e))
      case PureV(e)       => "pure" + paren(tr(e))
      case ApplyV(e1, e2) => paren(tr(e1)) + " <*> " + paren(tr(e2))
      case MoveXYV(e1, e2, e3) =>
        "moveXY" + paren(tr(e1) + ", " + tr(e2) + ", " + tr(e3))
      case WhenV(e1, e2, e3) =>
        "when" + paren(tr(e1) + ", " + tr(e2) + ", " + tr(e3))
      case BlankV        => "blank"
      case OverV(e1, e2) => paren(tr(e1) + "<+>" + tr(e2))

      // Values
      case UnitV                  => "()"
      case IntV(n)                => n.toString
      case BoolV(b)               => b.toString
      case ListV(l)               => l.map({ e: Expr => tr(e) }).toString
      case StringV(s)             => "\"" + s + "\""
      case PairV(v1, v2)          => (tr(v1), tr(v2)).toString
      case FunV(x, ty, e)         => tr(Lambda(x, ty, e))
      case RecV(f, x, tyx, ty, e) => tr(Rec(f, x, tyx, ty, e))
    }

    def trty(ty: Type): String = ty match {
      case UnitTy           => "Unit"
      case IntTy            => "Int"
      case BoolTy           => "Boolean"
      case StringTy         => "String"
      case FrameTy          => "Frame"
      case ListTy(ty)       => "List[" + trty(ty) + "]"
      case PairTy(ty1, ty2) => paren(trty(ty1) + ", " + trty(ty2))
      case FunTy(ty1, ty2)  => paren(trty(ty1) + " => " + trty(ty2))
      case SignalTy(ty)     => "Signal[" + trty(ty) + "]"
    }
  }

  val parser = new RabbitParser
  object Main {
    def typecheck(ast: Expr): Type =
      tyOf(Map.empty, ast);

    def showResult(
        ast: Expr,
        outputFilename: String,
        test: Boolean,
        sampleSolution: Boolean
    ) {
      println("AST:  " + ast.toString + "\n")
      try {
        print("Type Checking...");
        val ty = typecheck(ast);
        println("Done!");
        println("Type of Expression: " + ty.toString + "\n");
        (test, ty) match {
          case (true, _)                  => ()
          case (false, SignalTy(FrameTy)) => ()
          case (false, ty) => {
            sys.error(
              "Can only run animations of type signal[frame], not " + ty.toString
            )
          }
        }
      } catch {
        case e: Throwable => {
          println("Error: " + e)
          sys.exit(-1)
        }
      }
      try {
        println("Desugaring...");
        val core_ast = desugar(ast);
        println("Done!");
        println("Desugared AST: " + core_ast.toString + "\n");
        try {
          println("Evaluating...");
          var result = Eval.eval(core_ast)
          println("Done!");
          println("Evaluated AST: " + result.toString + "\n");
          if (test) {
            println(result)
            println(Translation.tr(result))
          } else {
            println("Writing to Scala file...");
            val fileWriter = new FileWriter(new File("RunRabbit.scala"))
            if (sampleSolution) {
              fileWriter.write(
                "import Assignment3.RabbitEDSL.Assignment3Embedded.DeepRabbitDSL._\n\n"
              )
            } else {
              fileWriter.write(
                "import Assignment3.RabbitEDSL.Assignment3Embedded.RabbitDSLImpl._\n\n"
              )
            }
            fileWriter.write("def anim = " + Translation.tr(result) + " \n")
            fileWriter.write(
              "saveToFile(anim, 20, \"" + outputFilename + "\")\n"
            )
            fileWriter.close()
          }
        } catch {
          case e: Throwable => println("Error: " + e)
        }
      } catch {
        case e: Throwable =>
          println("Error: " + e)
          println("Evaluating original AST...");
          print(Translation.tr(Eval.eval(ast)))
      }

    }
  }

  val FILENAME = "filename"
  val OUTPUT = "output"
  val TEST = "test"
  val SAMPLE = "sample"

  val defaultArgs = ListMap(
    FILENAME -> "",
    OUTPUT -> "output.gif",
    TEST -> "false",
    SAMPLE -> "false"
  )

  def main(args: Array[String]): Unit = {
    val argList = args.toList

    def readArgs(
        argList: List[String],
        optMap: ListMap[String, String]
    ): ListMap[String, String] = argList match {
      case Nil => optMap
      case "-o" :: outputName :: tail =>
        readArgs(tail, optMap + (OUTPUT -> outputName))
      case "-t" :: tail =>
        readArgs(tail, optMap + (TEST -> "true"))
      case "-s" :: tail =>
        readArgs(tail, optMap + (SAMPLE -> "true"))
      case fn :: _ => optMap + (FILENAME -> fn)
    }

    if (args.length == 0) {
      print("Usage: [-o output_filename] [-t] filename\n")
    } else {
      print("Parsing...");
      val argMap = readArgs(args.toList, defaultArgs)
      val ast = parser.parse(argMap(FILENAME))
      println("Done!");
      Main.showResult(
        ast,
        argMap(OUTPUT),
        argMap(TEST).toBoolean,
        argMap(SAMPLE).toBoolean
      )
    }
  }

}
