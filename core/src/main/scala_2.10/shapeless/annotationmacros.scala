/*
 * Copyright (c) 2015-9 Alexandre Archambault
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package shapeless

import scala.reflect.macros.{Context, whitebox}

case class CaseClassMacros210(ctx: Context) extends CaseClassMacros {
  override val c: whitebox.Context = ctx.asInstanceOf[whitebox.Context]
}

//@macrocompat.bundle
object AnnotationMacros {

  def someTpe(c: Context, ccm: CaseClassMacros210) = ccm.c.universe.typeOf[Some[_]].typeConstructor
  def noneTpe(c: Context, ccm: CaseClassMacros210) = ccm.c.universe.typeOf[None.type]

  // FIXME Most of the content of this method is cut-n-pasted from generic.scala
  def construct(c: Context, ccm: CaseClassMacros210)(tpe: ccm.c.Type): List[ccm.c.Tree] => ccm.c.Tree = {
    import ccm.c.universe._

    // FIXME Cut-n-pasted from generic.scala
    val sym = tpe.typeSymbol
    val isCaseClass = sym.asClass.isCaseClass
    def hasNonGenericCompanionMember(name: String): Boolean = {
      val mSym = sym.companionSymbol.typeSignature.member(newTermName(name))
      mSym != NoSymbol && !ccm.isNonGeneric(mSym)
    }

    if(isCaseClass || hasNonGenericCompanionMember("apply"))
      args => q"${ccm.companionRef(tpe)}(..$args)"
    else
      args => q"new $tpe(..$args)"
  }

  def materializeAnnotation[A: c.WeakTypeTag, T: c.WeakTypeTag](c: Context): c.Expr[Annotation[A, T]] = {
    val ccm = CaseClassMacros210(c)
    import ccm.c.universe._

    val annTpe = weakTypeOf[A]

    if (!ccm.isProduct(annTpe))
      ccm.abort(s"$annTpe is not a case class-like type")

    val construct0 = construct(c, ccm)(annTpe)

    val tpe = weakTypeOf[T]

    val annTreeOpt = tpe.typeSymbol.annotations.collectFirst {
      case ann if ann.tpe =:= annTpe => construct0(ann.scalaArgs.tail)
    }

    val tree = annTreeOpt match {
      case Some(annTree) =>
        q"_root_.shapeless.Annotation.mkAnnotation[$annTpe, $tpe]($annTree)"
      case None =>
        c.abort(c.enclosingPosition, s"No $annTpe annotation found on $tpe")
    }

    c.Expr(tree.asInstanceOf[c.Tree])
  }

  def materializeVariableAnnotations[A: c.WeakTypeTag, T: c.WeakTypeTag, Out <: HList](c: Context): c.Expr[Annotations.Aux[A, T, Out]] = {
    val tree = materializeAnnotations[A, T, Out](c)(false)
    c.Expr(tree)
  }

  def materializeTypeAnnotations[A: c.WeakTypeTag, T: c.WeakTypeTag, Out <: HList](c: Context): c.Expr[TypeAnnotations.Aux[A, T, Out]] = {
    val tree = materializeAnnotations[A, T, Out](c)(true)
    c.Expr(tree)
  }

  def materializeAnnotations[A: c.WeakTypeTag, T: c.WeakTypeTag, Out: c.WeakTypeTag](c: Context)(typeAnnotation: Boolean): c.Tree = {
    val ccm = CaseClassMacros210(c)
    import ccm.c.universe._

    val annTpe = weakTypeOf[A]

    if (!ccm.isProduct(annTpe))
      ccm.abort(s"$annTpe is not a case class-like type")

    val tpe = weakTypeOf[T]

    val annTreeOpts =
      if (ccm.isProduct(tpe)) {
        val constructorSyms = tpe
          .member(nme.CONSTRUCTOR)
          .asMethod
          .paramss
          .flatten
          .map { sym => sym.name.decodedName.toString -> sym }
          .toMap

        ccm.fieldsOf(tpe).map { case (name, _) =>
          val paramConstrSym = constructorSyms(name.decodedName.toString)

          if (typeAnnotation) collectTypeAnnotation(c, ccm)(annTpe, paramConstrSym)
          else collectVariableAnnotation(c, ccm)(annTpe, paramConstrSym)
        }
      } else if (ccm.isCoproduct(tpe))
        ccm.ctorsOf(tpe).map { cTpe =>
          if (typeAnnotation) collectTypeAnnotation(c, ccm)(annTpe, cTpe.typeSymbol)
          else collectVariableAnnotation(c, ccm)(annTpe, cTpe.typeSymbol)
        }
      else
        c.abort(c.enclosingPosition, s"$tpe is not case class like or the root of a sealed family of types")

    val wrapTpeTrees = annTreeOpts.map {
      case Some(annTree) => appliedType(someTpe(c, ccm), List(annTpe)) -> q"_root_.scala.Some($annTree)"
      case None => noneTpe(c, ccm) -> q"_root_.scala.None"
    }

    val outTpe = ccm.mkHListTpe(wrapTpeTrees.map { case (aTpe, _) => aTpe })
    val outTree = wrapTpeTrees.foldRight(q"_root_.shapeless.HNil": ccm.c.Tree) {
      case ((_, bound), acc) => pq"_root_.shapeless.::($bound, $acc)"
    }

    val tree = if (typeAnnotation) q"_root_.shapeless.TypeAnnotations.mkAnnotations[$annTpe, $tpe, $outTpe]($outTree)"
    else q"_root_.shapeless.Annotations.mkAnnotations[$annTpe, $tpe, $outTpe]($outTree)"

    tree.asInstanceOf[c.Tree]
  }

  def collectVariableAnnotation(c: Context, ccm: CaseClassMacros210)(annTpe: ccm.c.Type, s: ccm.c.Symbol): Option[ccm.c.Tree] = {
    val construct0 = construct(c, ccm)(annTpe)

    s.annotations.collectFirst {
      case ann if ann.tpe =:= annTpe => construct0(ann.scalaArgs.tail)
    }
  }

  def collectTypeAnnotation(c: Context, ccm: CaseClassMacros210)(annTpe: ccm.c.Type, s: ccm.c.Symbol): Option[ccm.c.Tree] = {
    import ccm.c.universe._

    val construct0 = construct(c, ccm)(annTpe)

    s.typeSignature match {
      case AnnotatedType(annots, _, _) =>
        annots.collectFirst {
          case ann if ann.tpe =:= annTpe => construct0(ann.scalaArgs.tail)
        }
      case _ => None
    }
  }
}
