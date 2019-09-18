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

import scala.reflect.macros.whitebox

@macrocompat.bundle
class AnnotationMacros(val c: whitebox.Context) extends CaseClassMacros {
  import c.universe._

  def someTpe = typeOf[Some[_]].typeConstructor
  def noneTpe = typeOf[None.type]

  // FIXME Most of the content of this method is cut-n-pasted from generic.scala
  def construct(tpe: Type): List[Tree] => Tree = {
    // FIXME Cut-n-pasted from generic.scala
    val sym = tpe.typeSymbol
    val isCaseClass = sym.asClass.isCaseClass
    def hasNonGenericCompanionMember(name: String): Boolean = {
      val mSym = sym.companion.typeSignature.member(TermName(name))
      mSym != NoSymbol && !isNonGeneric(mSym)
    }

    if(isCaseClass || hasNonGenericCompanionMember("apply"))
      args => q"${companionRef(tpe)}(..$args)"
    else
      args => q"new $tpe(..$args)"
  }

  def materializeAnnotation[A: WeakTypeTag, T: WeakTypeTag]: Tree = {
    val annTpe = weakTypeOf[A]

    if (!isProduct(annTpe))
      abort(s"$annTpe is not a case class-like type")

    val construct0 = construct(annTpe)

    val tpe = weakTypeOf[T]

    val annTreeOpt = tpe.typeSymbol.annotations.collectFirst {
      case ann if ann.tree.tpe =:= annTpe => construct0(ann.tree.children.tail)
    }

    annTreeOpt match {
      case Some(annTree) =>
        q"_root_.shapeless.Annotation.mkAnnotation[$annTpe, $tpe]($annTree)"
      case None =>
        abort(s"No $annTpe annotation found on $tpe")
    }
  }

  def materializeVariableAnnotations[A: WeakTypeTag, T: WeakTypeTag, Out: WeakTypeTag] = materializeAnnotations[A, T, Out](false)

  def materializeTypeAnnotations[A: WeakTypeTag, T: WeakTypeTag, Out: WeakTypeTag] = materializeAnnotations[A, T, Out](true)

  def materializeAnnotations[A: WeakTypeTag, T: WeakTypeTag, Out: WeakTypeTag](typeAnnotation: Boolean): Tree = {
    val annTpe = weakTypeOf[A]

    if (!isProduct(annTpe))
      abort(s"$annTpe is not a case class-like type")

    val tpe = weakTypeOf[T]

    val annTreeOpts =
      if (isProduct(tpe)) {
        val constructorSyms = tpe
          .member(termNames.CONSTRUCTOR)
          .asMethod
          .paramLists
          .flatten
          .map { sym => sym.name.decodedName.toString -> sym }
          .toMap

        fieldsOf(tpe).map { case (name, _) =>
          val paramConstrSym = constructorSyms(name.decodedName.toString)

          if (typeAnnotation) collectTypeAnnotation(annTpe, paramConstrSym)
          else collectVariableAnnotation(annTpe, paramConstrSym)
        }
      } else if (isCoproduct(tpe))
        ctorsOf(tpe).map { cTpe =>
          if (typeAnnotation) collectTypeAnnotation(annTpe, cTpe.typeSymbol)
          else collectVariableAnnotation(annTpe, cTpe.typeSymbol)
        }
      else
        abort(s"$tpe is not case class like or the root of a sealed family of types")

    val wrapTpeTrees = annTreeOpts.map {
      case Some(annTree) => appliedType(someTpe, annTpe) -> q"_root_.scala.Some($annTree)"
      case None => noneTpe -> q"_root_.scala.None"
    }

    val outTpe = mkHListTpe(wrapTpeTrees.map { case (aTpe, _) => aTpe })
    val outTree = wrapTpeTrees.foldRight(q"_root_.shapeless.HNil": Tree) {
      case ((_, bound), acc) => pq"_root_.shapeless.::($bound, $acc)"
    }

    if (typeAnnotation) q"_root_.shapeless.TypeAnnotations.mkAnnotations[$annTpe, $tpe, $outTpe]($outTree)"
    else q"_root_.shapeless.Annotations.mkAnnotations[$annTpe, $tpe, $outTpe]($outTree)"
  }

  def collectVariableAnnotation(annTpe: Type, s: Symbol): Option[Tree] = {
    val construct0 = construct(annTpe)

    s.annotations.collectFirst {
      case ann if ann.tree.tpe =:= annTpe => construct0(ann.tree.children.tail)
    }
  }

  def collectTypeAnnotation(annTpe: Type, s: Symbol): Option[Tree] = {
    val construct0 = construct(annTpe)

    s.typeSignature match {
      case AnnotatedType(annots, _) =>
        annots.collectFirst {
          case ann if ann.tree.tpe =:= annTpe => construct0(ann.tree.children.tail)
        }
      case _ => None
    }
  }
}
