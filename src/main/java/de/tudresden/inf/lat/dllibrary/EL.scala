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
import de.tudresden.inf.lat.dllibrary.FLE._
import de.tudresden.inf.lat.dllibrary.FLEsd._
import de.tudresden.inf.lat.dllibrary.FLEsdClassExpression._
import de.tudresden.inf.lat.dllibrary.OWLAPI._

object EL {

  implicit class ELClassExpression(classExpression: OWLClassExpression) extends FLEClassExpression(classExpression) {

    private lazy val isELClassExpression: Boolean = isELClassExpression(classExpression)

    private def isELClassExpression(c: OWLClassExpression): Boolean = {
      c match {
        case OWLThing                                   ⇒ true
        case OWLNothing                                 ⇒ true
        case Class(_)                                   ⇒ true
        case ObjectIntersectionOf(ds)                   ⇒ ds forall isELClassExpression
        case ObjectSomeValuesFrom(ObjectProperty(r), d) ⇒ isELClassExpression(d)
        case default                                    ⇒ false
      }
    }

    override protected def checkSyntax() {
      if (!isELClassExpression)
        throw new IllegalArgumentException("The class expression " + classExpression + " is not an EL class expression.")
    }

    lazy val reduction = reduced()

    private def reduced(): OWLClassExpression = {
      checkSyntax()
      if (classExpression.isOWLNothing)
        OWLNothing
      else if (classExpression.isOWLThing)
        OWLThing
      else {
        classExpression.asConjunctSet.asScala
          .filter({
            case OWLThing ⇒ false
            case Class(_) ⇒ true
            case ObjectSomeValuesFrom(roleName @ ObjectProperty(_), filler) ⇒ {
              classExpression.asConjunctSet.asScala
                .forall({
                  case ObjectSomeValuesFrom(otherRoleName @ ObjectProperty(_), otherFiller) if {
                    (roleName equals otherRoleName) && !(filler equals otherFiller)
                  } ⇒ !(filler subsumes otherFiller)
                  case default ⇒ true
                })
              true
            }
            case default ⇒ throw new RuntimeException
          })
          .map({
            case conceptName @ Class(_) ⇒ conceptName
            case ObjectSomeValuesFrom(roleName @ ObjectProperty(_), filler) ⇒
              ObjectSomeValuesFrom(roleName, filler.reduction)
          })
          .foldLeft[OWLClassExpression](OWLThing)(_ and _)
      }
    }

    def upperNeighbors(): collection.Set[OWLClassExpression] = {
      checkSyntax()
      if (classExpression.isOWLThing) {
        Set()
      } else {
        reduction.asConjunctSet.asScala.map(ELClassExpression(reduction).upperNeighborForConjunct(_))
      }
    }

    private def upperNeighborForConjunct(conjunct: OWLClassExpression): OWLClassExpression = {
      conjunct match {
        case OWLThing   ⇒ throw new IllegalArgumentException
        case OWLNothing ⇒ throw new IllegalArgumentException
        case conceptName @ Class(_) ⇒ {
          reduction.asConjunctSet.asScala
            .filter(conjunct ⇒ !(conjunct equals conceptName))
            .foldLeft[OWLClassExpression](OWLThing)(_ and _)
        }
        case ObjectIntersectionOf(_) ⇒ throw new RuntimeException
        case existentialRestriction @ ObjectSomeValuesFrom(roleName @ ObjectProperty(_), filler) ⇒ {
          reduction.asConjunctSet.asScala
            .filter(conjunct ⇒ !(conjunct equals existentialRestriction))
            .foldLeft[OWLClassExpression](OWLThing)(_ and _) and
            filler.upperNeighbors
            .filter(upperNeighbor ⇒ {
              reduction.asConjunctSet.asScala
                .map({
                  case otherExistentialRestriction
                    @ ObjectSomeValuesFrom(otherRoleName @ ObjectProperty(_), otherFiller) if {
                    !(otherExistentialRestriction equals existentialRestriction) &&
                      (otherRoleName equals roleName)
                  } ⇒ otherFiller
                })
                .forall(otherFiller ⇒ !(upperNeighbor subsumes otherFiller))
            })
            .map(roleName some _)
            .foldLeft[OWLClassExpression](OWLThing)(_ and _)
        }
        case default ⇒ throw new IllegalArgumentException
      }
    }

    def lowerNeighbors(signature: collection.Set[OWLEntity]): collection.Set[OWLClassExpression] = {
      checkSyntax()
      if (classExpression.isOWLNothing) {
        Set()
      } else {
        val reduction = this.reduced
        val lowerNeighbors = new collection.mutable.HashSet[OWLClassExpression]
        signature.foreach({
          case conceptName @ Class(_) ⇒ {
            if (!(classExpression containsConjunct conceptName)) {
              val lowerNeighbor = this.clone and conceptName
              lowerNeighbors.add(lowerNeighbor)
            }
          }
          case roleName @ ObjectProperty(_) ⇒ {
            val filter = reduction.asConjunctSet.asScala
              .map({
                case ObjectSomeValuesFrom(otherRoleName @ ObjectProperty(_), filler) if (roleName equals otherRoleName) ⇒ filler
              })
            val choices =
              new collection.mutable.HashMap[OWLClassExpression, collection.mutable.Set[OWLClassExpression]] with collection.mutable.MultiMap[OWLClassExpression, OWLClassExpression]
            val subsumees =
              new collection.mutable.HashMap[OWLClassExpression, collection.mutable.Set[OWLClassExpression]] with collection.mutable.MultiMap[OWLClassExpression, OWLClassExpression]
            filter foreach (f ⇒ {
              f.lowerNeighbors(signature) foreach (l ⇒ {
                val c = l without f
                choices.addBinding(f, c)
                filter filter { c subsumes _ } foreach { subsumees.addBinding(c, _) }
              })
            })
            filter.subsets foreach (fs ⇒ {
              (choices filter {
                case (k, _) ⇒ fs contains k
              } map {
                case (k, v) ⇒
                  v filter {
                    x ⇒
                      fs filter {
                        f ⇒ !(k equals f)
                      } forall {
                        f ⇒ subsumees(x) contains f
                      }
                  }
              }).foldLeft[collection.Set[collection.Set[OWLClassExpression]]](Set(Set()))((xs, ys) ⇒ xs flatMap { x ⇒ ys map { y ⇒ x + y } })
                .foreach(fs ⇒ {
                  if (filter filter {
                    f ⇒ !(fs contains f)
                  } forall {
                    f ⇒ !(fs forall { x ⇒ subsumees(x) contains f })
                  }) {
                    val d = fs.foldLeft[OWLClassExpression](OWLThing)(_ and _)
                    val lowerNeighbor = this.clone and (roleName some d)
                    lowerNeighbors.add(lowerNeighbor)
                  }
                })
            })
          }
        })
        lowerNeighbors
      }
    }

    lazy val rank = computeRank()

    private def computeRank(): Long = {
      checkSyntax()
      if (this.classExpression.isOWLNothing)
        Long.MaxValue
      else {
        var r = 0
        var c = this.reduced
        while (!c.isOWLThing) {
          c = ELClassExpression(c).upperNeighborForConjunct(c.asConjunctSet.asScala.head)
          r += 1
        }
        r
      }
    }

    def without(other: ELClassExpression): OWLClassExpression = {
      this.checkSyntax()
      other.checkSyntax()
      if (this subsumes other)
        OWLThing
      else if (this.classExpression.isOWLNothing)
        OWLNothing
      else
        classExpression.asConjunctSet.asScala
          .filter({
            case OWLThing   ⇒ false
            case OWLNothing ⇒ true
            case conceptName @ Class(_) ⇒ {
              !(other.classExpression containsConjunct conceptName)
            }
            case existentialRestriction @ ObjectSomeValuesFrom(ObjectProperty(_), _) ⇒ {
              !(other isSubsumedBy existentialRestriction)
            }
            case default ⇒ throw new IllegalArgumentException
          })
          .foldLeft[OWLClassExpression](OWLThing)(_ and _)
    }

    implicit class ImplicitBoolean(b: Boolean) {
      def ->(c: Boolean) = !b || c
    }

    def satisfies(axiom: OWLSubClassOfAxiom): Boolean = {
      this.checkSyntax()
      (classExpression isSubsumedBy axiom.getSubClass) -> (classExpression isSubsumedBy axiom.getSuperClass)
    }

    def canBeSimulatedIn(other: ELClassExpression): Boolean = {
      this.checkSyntax()
      other.checkSyntax()
      (this.roleDepth <= other.roleDepth) &&
        ((this subsumes other) ||
          (other.classExpression.asConjunctSet.asScala.exists({
            case ObjectSomeValuesFrom(ObjectProperty(_), filler) ⇒ this canBeSimulatedIn filler
            case default                                         ⇒ false
          })))
    }

    def isSemanticallySmaller(other: ELClassExpression): Boolean = {
      this.checkSyntax()
      other.checkSyntax()
      (this.roleDepth <= other.roleDepth) &&
        !(this isSubsumedBy other) &&
        (this canBeSimulatedIn other)
    }

  }

  /**
   * This method is not proven to be sound.
   */
  def reduceConclusion(axiom: OWLSubClassOfAxiom): OWLSubClassOfAxiom = {
    val subClass = axiom.getSubClass.reduction
    val superClass = axiom.getSuperClass.reduction
    def recurse(classExpression: OWLClassExpression): OWLClassExpression = {
      superClass.asConjunctSet.asScala.map({
        case a @ Class(_) ⇒ a
        case ObjectSomeValuesFrom(roleName @ ObjectProperty(_), filler) ⇒ {
          if (filler isSubsumedBy subClass)
            ObjectSomeValuesFrom(roleName, recurse((filler without superClass and subClass).reduction))
          else
            ObjectSomeValuesFrom(roleName, recurse(filler))
        }
        case default ⇒ throw new RuntimeException
      }).foldLeft[OWLClassExpression](OWLThing)(_ and _)
    }
    subClass SubClassOf recurse(superClass)
  }

  private def specificCompliantGeneralizations(policy: collection.Set[OWLClassExpression]): collection.Set[OWLClassExpression] = {
    ???
  }

  def optimalCompliantGeneralizations(policy: collection.Set[OWLClassExpression]): collection.Set[OWLClassExpression] = {
    ???
  }

}
