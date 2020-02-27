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
import de.tudresden.inf.lat.dllibrary.FLEsdClassExpression._

object FLE {

  implicit class FLEClassExpression(val classExpression: OWLClassExpression) extends Cloneable {

    override def clone(): OWLClassExpression = {
      new OWLObjectDuplicator(OWLManager.getOWLDataFactory).duplicateObject(classExpression).asInstanceOf[OWLClassExpression]
    }

    private lazy val isFLEClassExpression: Boolean = isFLEClassExpression(classExpression)

    private def isFLEClassExpression(c: OWLClassExpression): Boolean = {
      c match {
        case OWLThing                                   ⇒ true
        case OWLNothing                                 ⇒ true
        case Class(_)                                   ⇒ true
        case ObjectIntersectionOf(ds)                   ⇒ ds forall isFLEClassExpression
        case ObjectSomeValuesFrom(ObjectProperty(r), d) ⇒ isFLEClassExpression(d)
        case ObjectAllValuesFrom(ObjectProperty(r), d)  ⇒ isFLEClassExpression(d)
        case default                                    ⇒ false
      }
    }

    protected def checkSyntax() {
      if (!isFLEClassExpression)
        throw new IllegalArgumentException("The class expression " + classExpression + " is not an FLE class expression.")
    }

    lazy val roleDepth = computeRoleDepth()

    private def computeRoleDepth(): Int = {
      checkSyntax()
      classExpression.asConjunctSet.asScala
        .map({
          case OWLThing                                        ⇒ 0
          case OWLNothing                                      ⇒ 0
          case Class(_)                                        ⇒ 0
          case ObjectSomeValuesFrom(ObjectProperty(_), filler) ⇒ 1 + filler.roleDepth
          case ObjectAllValuesFrom(ObjectProperty(_), filler)  ⇒ 1 + filler.roleDepth
          case default                                         ⇒ throw new IllegalArgumentException
        })
        .max
    }

    def lcs(other: FLEClassExpression): OWLClassExpression = {
      this.checkSyntax()
      other.checkSyntax()
      val roleDepth = Math.min(this.roleDepth, other.roleDepth)
      (FLEsdClassExpression(this) lcs FLEsdClassExpression(other)).approximate(roleDepth)
    }

  }

}
