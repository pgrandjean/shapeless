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

import scala.language.experimental.macros

/**
 * Evidence that type `T` has annotation `A`, and provides an instance of the annotation.
 *
 * If type `T` has an annotation of type `A`, then an implicit `Annotation[A, T]` can be found, and its `apply` method
 * provides an instance of the annotation.
 *
 * Example:
 * {{{
 *   case class First(i: Int)
 *
 *   @First(3) trait Something
 *   
 *
 *   val somethingFirst = Annotation[First, Something].apply()
 *   assert(somethingFirst == First(3))
 * }}}
 *
 * @tparam A: annotation type
 * @tparam T: annotated type
 *
 * @author Alexandre Archambault
 */
trait Annotation[A, T] extends Serializable {
  def apply(): A
}

object Annotation {
  def apply[A,T](implicit annotation: Annotation[A, T]): Annotation[A, T] = annotation

  def mkAnnotation[A, T](annotation: => A): Annotation[A, T] =
    new Annotation[A, T] {
      def apply() = annotation
    }

  implicit def materialize[A, T]: Annotation[A, T] = macro AnnotationMacros.materializeAnnotation[A, T]
}

/**
 * Provides the annotations of type `A` of the fields or constructors of case class-like or sum type `T`.
 *
 * If type `T` is case class-like, this type class inspects its fields and provides their annotations of type `A`. If
 * type `T` is a sum type, its constructor types are looked for annotations.
 *
 * Type `Out` is an HList having the same number of elements as `T` (number of fields of `T` if `T` is case class-like,
 * or number of constructors of `T` if it is a sum type). It is made of `None.type` (no annotation on corresponding
 * field or constructor) and `Some[A]` (corresponding field or constructor is annotated).
 *
 * Method `apply` provides an HList of type `Out` made of `None` (corresponding field or constructor not annotated)
 * or `Some(annotation)` (corresponding field or constructor has annotation `annotation`).
 *
 * Note that annotation types must be case class-like for this type class to take them into account.
 *
 * Example:
 * {{{
 *   case class First(s: String)
 *
 *   case class CC(i: Int, @First("a") s: String)
 *
 *   sealed trait Base
 *   @First("b") case class BaseI(i: Int) extends Base
 *   case class BaseS(s: String) extends Base
 *
 *
 *   val ccFirsts = Annotations[First, CC]
 *   val baseFirsts = Annotations[First, Base]
 *
 *   // ccFirsts.Out is  None.type :: Some[First] :: HNil
 *   // ccFirsts.apply() is
 *   //   None :: Some(First("a")) :: HNil
 *
 *   // baseFirsts.Out is  Some[First] :: None.type :: HNil
 *   // baseFirsts.apply() is
 *   //   Some(First("b")) :: None :: HNil
 * }}}
 *
 * @tparam A: annotation type
 * @tparam T: case class-like or sum type, whose fields or constructors are annotated
 *
 * @author Alexandre Archambault
 */
trait Annotations[A,T] extends DepFn0 with Serializable {
  type Out <: HList
}

object Annotations {
  def apply[A,T](implicit annotations: Annotations[A,T]): Aux[A, T, annotations.Out] = annotations

  type Aux[A, T, Out0 <: HList] = Annotations[A, T] { type Out = Out0 }

  def mkAnnotations[A, T, Out0 <: HList](annotations: => Out0): Aux[A, T, Out0] =
    new Annotations[A, T] {
      type Out = Out0
      def apply() = annotations
    }

  implicit def materialize[A, T, Out <: HList]: Aux[A, T, Out] = macro AnnotationMacros.materializeVariableAnnotations[A, T, Out]
}

/**
 * Provides the type annotations of type `A` of the fields or constructors of case class-like or sum type `T`.
 *
 * If type `T` is case class-like, this type class inspects its fields and provides their type annotations of type `A`. If
 * type `T` is a sum type, its constructor types are looked for type annotations.
 *
 * Type `Out` is an HList having the same number of elements as `T` (number of fields of `T` if `T` is case class-like,
 * or number of constructors of `T` if it is a sum type). It is made of `None.type` (no annotation on corresponding
 * field or constructor) and `Some[A]` (corresponding field or constructor is annotated).
 *
 * Method `apply` provides an HList of type `Out` made of `None` (corresponding field or constructor not annotated)
 * or `Some(annotation)` (corresponding field or constructor has annotation `annotation`).
 *
 * Note that type annotations must be case class-like for this type class to take them into account.
 *
 * Example:
 * {{{
 *   case class First(s: String)
 *
 *   case class CC(i: Int, s: String @First("a"))
 *
 *   val ccFirsts = TypeAnnotations[First, CC]
 *
 *   // ccFirsts.Out is  None.type :: Some[First] :: HNil
 *   // ccFirsts.apply() is
 *   //   None :: Some(First("a")) :: HNil
 *
 * }}}
 *
 * This implementation is based on [[shapeless.Annotations]] by Alexandre Archambault.
 *
 * @tparam A: type annotation type
 * @tparam T: case class-like or sum type, whose fields or constructors are annotated
 *
 * @author Patrick Grandjean
 */
trait TypeAnnotations[A,T] extends DepFn0 with Serializable {
  type Out <: HList
}

object TypeAnnotations {
  def apply[A,T](implicit annotations: TypeAnnotations[A,T]): Aux[A, T, annotations.Out] = annotations

  type Aux[A, T, Out0 <: HList] = TypeAnnotations[A, T] { type Out = Out0 }

  def mkAnnotations[A, T, Out0 <: HList](annotations: => Out0): Aux[A, T, Out0] =
    new TypeAnnotations[A, T] {
      type Out = Out0
      def apply() = annotations
    }

  implicit def materialize[A, T, Out <: HList]: Aux[A, T, Out] = macro AnnotationMacros.materializeTypeAnnotations[A, T, Out]
}
