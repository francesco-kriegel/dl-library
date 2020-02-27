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

import org.phenoscape.scowl._
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.OWLClass
import org.semanticweb.owlapi.model.OWLClassExpression
import org.semanticweb.owlapi.model.OWLObjectProperty
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom
import org.semanticweb.owlapi.util.OWLObjectDuplicator

import collection.JavaConverters._
import org.semanticweb.owlapi.model.OWLEntity
import de.tudresden.inf.lat.dllibrary.FLEsd._
import de.tudresden.inf.lat.dllibrary.Util._

trait ELsiClosureOperator extends Function[ELsiClassExpression[_], ELsiClassExpression[_]] {

  def infimum(other: ELsiClosureOperator): ELsiClosureOperator = {
    classExpression ⇒ (this(classExpression) lcs other(classExpression)).withIntegerVariables.asELsiClassExpression
  }

  def supremum(other: ELsiClosureOperator): ELsiClosureOperator = {
    classExpression ⇒ fixedPoint[ELsiClassExpression[_]](this andThen other, _ isSubsumedBy _)(classExpression).withIntegerVariables.asELsiClassExpression
  }

}

object ELsi {

  implicit class ELsiTBox(axioms: collection.Set[OWLSubClassOfAxiom]) extends ELsiClosureOperator {

    def apply(classExpression: ELsiClassExpression[_]): ELsiClassExpression[_] = {
      (classExpression saturate axioms).withIntegerVariables.asELsiClassExpression
    }
    
    def entails(axiom: OWLSubClassOfAxiom): Boolean = {
      this(axiom.getSubClass) isSubsumedBy axiom.getSuperClass
    }

  }

}

object ELsiClassExpression {

  def apply[V](variable: V, descriptionAxioms: DescriptionAxiom[V]*): ELsiClassExpression[V] = {
    val classExpression =
      new ELsiClassExpression[V](
        variable,
        new collection.mutable.HashMap[V, collection.mutable.Set[OWLClass]] with collection.mutable.MultiMap[V, OWLClass],
        new collection.mutable.HashMap[V, collection.mutable.Set[QuantifiedVariable[V]]] with collection.mutable.MultiMap[V, QuantifiedVariable[V]])
    descriptionAxioms foreach classExpression.addDescriptionAxiom
    classExpression
  }
  
  implicit def apply(classExpression: OWLClassExpression): ELsiClassExpression[OWLClassExpression] = {
    FLEsdClassExpression(classExpression).asELsiClassExpression
  }

}

class ELsiClassExpression[V](
  variable:          V,
  initialTypes:      collection.Map[V, collection.Set[OWLClass]] with collection.mutable.MultiMap[V, OWLClass],
  initialSuccessors: collection.Map[V, collection.Set[QuantifiedVariable[V]]] with collection.mutable.MultiMap[V, QuantifiedVariable[V]])
  extends FLEsdClassExpression[V](variable, initialTypes, initialSuccessors) {

  override def addDescriptionAxiom(axiom: DescriptionAxiom[V]) {
    axiom match {
      case TypeDescriptionAxiom(v, c)               ⇒ types.addBinding(v, c)
      case SuccessorDescriptionAxiom(v, SomeV(r, w)) ⇒ successors.addBinding(v, SomeV(r, w))
      case SuccessorDescriptionAxiom(v, OnlyV(r, w)) ⇒ throw new IllegalArgumentException
    }
  }

  def saturate(axioms: collection.Set[OWLSubClassOfAxiom]): ELsiClassExpression[Either[V, OWLClassExpression]] = {
    val saturation = ELsiClassExpression[Either[V, OWLClassExpression]](Left(this.rootVariable))
    this.descriptionAxioms.foreach({
      case TypeDescriptionAxiom(v, c)               ⇒ saturation.addDescriptionAxiom(Left(v) Type c)
      case SuccessorDescriptionAxiom(v, SomeV(r, w)) ⇒ saturation.addDescriptionAxiom(Left(v) Successor SomeV(r, Left(w)))
      case default                                  ⇒ throw new IllegalArgumentException
    })
    var changed = true
    while (changed) {
      changed = false
      saturation.variables.foreach(variable ⇒
        axioms.foreach(axiom ⇒
          if ((saturation.rootedAt(variable) isSubsumedBy axiom.getSubClass) &&
            !(saturation.rootedAt(variable) isSubsumedBy axiom.getSuperClass)) {
            saturation.insert(variable, axiom.getSuperClass, Right(_))
            changed = true
          }))
    }
    saturation
  }

}
