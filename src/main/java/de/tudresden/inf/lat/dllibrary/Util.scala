/*-
 * #%L
 * DL Library
 * %%
 * Copyright (C) 2020 Francesco Kriegel
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

package de.tudresden.inf.lat.dllibrary

object Util {

  def fixedPoint[A](monotoneFunction: A ⇒ A, equivalencePredicate: (A, A) ⇒ Boolean = (a1: A, a2: A) ⇒ a1 equals a2) =
    (a: A) ⇒ {
      var result = a
      var continue = true
      while (continue) {
        val next = monotoneFunction(result)
        continue = !equivalencePredicate(result, next)
        result = next
      }
      result
    }

  def cartesianProduct[T](sets: collection.Set[collection.Set[T]]): collection.Set[collection.Set[T]] = {
    if (sets.isEmpty)
      Set.empty[collection.Set[T]]
    else {
      val seed: collection.Set[collection.Set[T]] = Set(Set())
      val foldFunction: ((collection.Set[collection.Set[T]], collection.Set[T]) ⇒ collection.Set[collection.Set[T]]) = {
        (xs: collection.Set[collection.Set[T]], ys: collection.Set[T]) ⇒ xs.flatMap((x: collection.Set[T]) ⇒ ys.map((y: T) ⇒ x + y))
      }
      sets.foldLeft(seed)(foldFunction)
    }
  }

  implicit class LocalSet[A](given: collection.Set[A]) {
    def strictSubsetOf(other: collection.Set[A]): Boolean = {
      (given subsetOf other) && (given.size < other.size)
    }
  }

  implicit class LocalMultiMap[A, B](given: collection.Map[A, collection.mutable.Set[B]] with collection.mutable.MultiMap[A, B]) {
    def foreachBinding(f: (A, B) ⇒ Unit): Unit = {
      given.foreach({ case (key, values) ⇒ values.foreach(value ⇒ f(key, value)) })
    }
  }

}
