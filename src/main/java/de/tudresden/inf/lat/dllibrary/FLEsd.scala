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

object FLEsd {

}

object FLEsdClassExpression {

  implicit def apply(classExpression: OWLClassExpression): FLEsdClassExpression[OWLClassExpression] = {
    val c = FLEsdClassExpression[OWLClassExpression](classExpression)
    c.insert(classExpression, classExpression, identity)
    c
  }

  implicit def apply(classExpression: FLEClassExpression): FLEsdClassExpression[OWLClassExpression] = {
    FLEsdClassExpression(classExpression.classExpression)
  }

  def apply[V](variable: V, descriptionAxioms: DescriptionAxiom[V]*): FLEsdClassExpression[V] = {
    val classExpression =
      new FLEsdClassExpression[V](
        variable,
        new collection.mutable.HashMap[V, collection.mutable.Set[OWLClass]] with collection.mutable.MultiMap[V, OWLClass],
        new collection.mutable.HashMap[V, collection.mutable.Set[QuantifiedVariable[V]]] with collection.mutable.MultiMap[V, QuantifiedVariable[V]])
    descriptionAxioms foreach classExpression.addDescriptionAxiom
    classExpression
  }

  //  def unapply[V](classExpression: FLEsdClassExpression[V]): Option[(_ <: V, collection.Set[DescriptionAxiom[_ <: V]])] = {
  //    Option.apply[(V, collection.Set[DescriptionAxiom[V]])](classExpression.rootVariable, classExpression.descriptionAxioms)
  //  }

}

sealed trait QuantifiedVariable[+V]
case class SomeV[+V](r: OWLObjectProperty, v: V) extends QuantifiedVariable[V]
case class OnlyV[+V](r: OWLObjectProperty, v: V) extends QuantifiedVariable[V]

sealed trait DescriptionAxiom[+V]
case class TypeDescriptionAxiom[+V](v: V, c: OWLClass) extends DescriptionAxiom[V]
case class SuccessorDescriptionAxiom[+V](v: V, w: QuantifiedVariable[V]) extends DescriptionAxiom[V]

class FLEsdClassExpression[V](
  val rootVariable: V,
  val types:        collection.Map[V, collection.Set[OWLClass]] with collection.mutable.MultiMap[V, OWLClass],
  val successors:   collection.Map[V, collection.Set[QuantifiedVariable[V]]] with collection.mutable.MultiMap[V, QuantifiedVariable[V]])
  extends OWLClassExpression with Cloneable {

  implicit class LocalOWLObjectProperty[V](self: OWLObjectProperty) {
    def someV(variable: V) = SomeV(self, variable)
    def onlyV(variable: V) = OnlyV(self, variable)
  }

  implicit class Variable[V](v: V) {
    def Type(c: OWLClass) = TypeDescriptionAxiom(v, c)
    def Successor(w: QuantifiedVariable[V]) = SuccessorDescriptionAxiom(v, w)
  }

  def typesOf(variable: V) = types(variable)

  def successorsOf(variable: V) = successors(variable)

  def addDescriptionAxiom(axiom: DescriptionAxiom[V]) {
    axiom match {
      case TypeDescriptionAxiom(v, c)      ⇒ types.addBinding(v, c)
      case SuccessorDescriptionAxiom(v, w) ⇒ successors.addBinding(v, w)
    }
  }

  def descriptionAxioms(): collection.Set[DescriptionAxiom[V]] = {
    types.par.foldRight[Set[TypeDescriptionAxiom[V]]](Set())({
      case ((variable, owlClasses), outerAxioms) ⇒ {
        outerAxioms ++ owlClasses.par.foldRight[Set[TypeDescriptionAxiom[V]]](Set())(
          (owlClass, innerAxioms) ⇒ innerAxioms + (variable Type owlClass))
      }
    }) ++ successors.par.foldRight[Set[SuccessorDescriptionAxiom[V]]](Set())({
      case ((variable, successors), outerAxioms) ⇒ {
        outerAxioms ++ successors.par.foldRight[Set[SuccessorDescriptionAxiom[V]]](Set())(
          (successor, innerAxioms) ⇒ innerAxioms + (variable Successor successor))
      }
    })
  }

  def variables(): collection.Set[V] = {
    types.keySet ++ successors.par.foldRight[Set[V]](Set())({
      case ((sourceVariable, successors), outerVariables) ⇒
        (outerVariables + sourceVariable) ++ successors.par.foldRight[Set[V]](Set())({
          case (SomeV(_, targetVariable), innerVariables) ⇒ innerVariables + targetVariable
          case (OnlyV(_, targetVariable), innerVariables) ⇒ innerVariables + targetVariable
        })
    })
  }

  protected def insert(position: V, classExpression: OWLClassExpression, positionMapping: OWLClassExpression ⇒ V) {
    // if ((position equals positionMapping(c)) && (variables contains position))
    val cycleDetection = new collection.mutable.HashMap[V, collection.mutable.Set[OWLClassExpression]] with collection.mutable.MultiMap[V, OWLClassExpression]
    if (!((cycleDetection get position) contains classExpression)) {
      cycleDetection.addBinding(position, classExpression)
      classExpression match {
        case OWLThing                 ⇒ {}
        case OWLNothing               ⇒ addDescriptionAxiom(position Type OWLNothing)
        case Class(a)                 ⇒ addDescriptionAxiom(position Type Class(a))
        case ObjectIntersectionOf(ds) ⇒ ds foreach { insert(position, _, positionMapping) }
        case ObjectSomeValuesFrom(ObjectProperty(r), d) ⇒ {
          addDescriptionAxiom(position Successor SomeV(ObjectProperty(r), positionMapping(d)))
          insert(positionMapping(d), d, positionMapping)
        }
        case ObjectAllValuesFrom(ObjectProperty(r), d) ⇒ {
          addDescriptionAxiom(position Successor OnlyV(ObjectProperty(r), positionMapping(d)))
          insert(positionMapping(d), d, positionMapping)
        }
        case ObjectMinCardinality(n, ObjectProperty(r), d) if (n equals 1) ⇒ {
          addDescriptionAxiom(position Successor SomeV(ObjectProperty(r), positionMapping(d)))
          insert(positionMapping(d), d, positionMapping)
        }
        case ObjectMaxCardinality(0, ObjectProperty(r), OWLThing) ⇒ {
          addDescriptionAxiom(position Successor OnlyV(ObjectProperty(r), positionMapping(OWLNothing)))
          insert(positionMapping(OWLNothing), OWLNothing, positionMapping)
        }
        case ObjectExactCardinality(0, ObjectProperty(r), OWLThing) ⇒ {
          addDescriptionAxiom(position Successor OnlyV(ObjectProperty(r), positionMapping(OWLNothing)))
          insert(positionMapping(OWLNothing), OWLNothing, positionMapping)
        }
        case c: FLEsdClassExpression[_] ⇒ {
          c.typesOf(c.rootVariable) foreach { a ⇒ addDescriptionAxiom(position Type a) }
          c.successorsOf(c.rootVariable) foreach {
            case SomeV(r, w) ⇒ {
              val d = c.rootedAt(w)
              addDescriptionAxiom(position Successor SomeV(r, positionMapping(d)))
              insert(positionMapping(d), d, positionMapping)
            }
            case OnlyV(r, w) ⇒ {
              val d = c.rootedAt(w)
              addDescriptionAxiom(position Successor OnlyV(r, positionMapping(d)))
              insert(positionMapping(d), d, positionMapping)
            }
          }
        }
        case default ⇒ throw new IllegalArgumentException
      }
    }
  }

  def normalize(): FLEsdClassExpression[Set[V]] = {
    val normalization = FLEsdClassExpression[Set[V]](Set(this.rootVariable))
    def insertIntoNormalization(vs: Set[V]) {
      vs foreach { v ⇒ this.typesOf(v) foreach { c ⇒ normalization.addDescriptionAxiom(vs Type c) } }
      getObjectPropertiesInSignatureAsScala foreach (r ⇒ {
        val ws = vs.foldLeft[Set[V]](Set())((xs, v) ⇒ {
          xs ++ this.successorsOf(v).foldLeft[Set[V]](Set())({
            case (ys, OnlyV(s, w)) ⇒ if (r equals s) ys + w else ys
            case (ys, SomeV(_, _)) ⇒ ys
          })
        })
        normalization.addDescriptionAxiom(vs Successor OnlyV(r, ws))
        vs foreach (v ⇒ {
          this.successorsOf(v) foreach {
            case SomeV(s, w) if (r equals s) ⇒ { normalization.addDescriptionAxiom(vs Successor SomeV(r, ws + w)) }
            case default                    ⇒ {}
          }
        })
      })
    }
    insertIntoNormalization(normalization.rootVariable)
    normalization
  }

  def reduce(): FLEsdClassExpression[V] = ???

  override def clone(): FLEsdClassExpression[V] = {
    val clone = FLEsdClassExpression[V](this.rootVariable)
    this.descriptionAxioms foreach { clone.addDescriptionAxiom(_) }
    clone
  }

  def withIntegerVariables(): FLEsdClassExpression[Integer] = {
    val f = new collection.mutable.HashMap[V, Integer]
    var n = 0
    this.variables.seq foreach { variable ⇒ { f.put(variable, n); n += 1 } }
    val renaming = FLEsdClassExpression[Integer](f(this.rootVariable))
    descriptionAxioms foreach {
      case TypeDescriptionAxiom(v, c)               ⇒ renaming.addDescriptionAxiom(f(v) Type c)
      case SuccessorDescriptionAxiom(v, SomeV(r, w)) ⇒ renaming.addDescriptionAxiom(f(v) Successor SomeV(r, f(w)))
      case SuccessorDescriptionAxiom(v, OnlyV(r, w)) ⇒ renaming.addDescriptionAxiom(f(v) Successor OnlyV(r, f(w)))
    }
    renaming
  }

  protected def approximate(variable: V, roleDepth: Int): OWLClassExpression = {
    val rootApproximation = typesOf(variable).fold[OWLClassExpression](OWLThing)((c, d) ⇒ c and d)
    if (roleDepth == 0) rootApproximation
    else rootApproximation and successorsOf(variable).aggregate[OWLClassExpression](OWLThing)(
      (c, successor) ⇒ successor match {
        case SomeV(r, w) ⇒ c and (r some approximate(w, roleDepth - 1))
        case OnlyV(r, w) ⇒ c and (r only approximate(w, roleDepth - 1))
      },
      (c, d) ⇒ c and d)
  }

  def approximate(roleDepth: Int): OWLClassExpression = approximate(rootVariable, roleDepth)

  protected def subsumes[W](other: FLEsdClassExpression[W], thisVariable: V, otherVariable: W): Boolean = {
    if (other.isOWLNothing) true
    else if (this.isOWLThing) true
    else if (this.isOWLNothing) false
    else {
      def simulationExists(v: V, w: W, partialSimulation: Set[(V, W)]): Boolean = {
        if (partialSimulation contains (v, w)) true
        else if (!(this.typesOf(v) subsetOf other.typesOf(w))) false
        else {
          this.successorsOf(v).par forall {
            case SomeV(r, x) ⇒ {
              other.successorsOf(w).par exists {
                case SomeV(s, y) if (r equals s) ⇒ { simulationExists(x, y, partialSimulation + ((v, w))) }
                case default                    ⇒ false
              }
            }
            case OnlyV(r, x) ⇒ {
              other.successorsOf(w).par exists {
                case OnlyV(s, y) if (r equals s) ⇒ { simulationExists(x, y, partialSimulation + ((v, w))) }
                case default                    ⇒ false
              }
            }
            case default ⇒ false
          }
        }
      }
      simulationExists(thisVariable, otherVariable, Set[(V, W)]())
    }
  }

  def subsumes[W](other: FLEsdClassExpression[W]): Boolean = {
    val otherNormalized = other.normalize
    subsumes(otherNormalized, this.rootVariable, otherNormalized.rootVariable)
  }

  def isSubsumedBy[W](other: FLEsdClassExpression[W]): Boolean = {
    other subsumes this
  }

  def isEquivalentTo[W](other: FLEsdClassExpression[W]): Boolean = {
    (this subsumes other) && (other subsumes this)
  }

  def rootedAt(variable: V) = {
    new FLEsdClassExpression[V](variable, this.types, this.successors)
  }

  def lcs[W](other: FLEsdClassExpression[W]): FLEsdClassExpression[(Set[V], Set[W])] = {
    val thisNormalized = this.normalize
    val otherNormalized = other.normalize
    val leastCommonSubsumer = FLEsdClassExpression((thisNormalized.rootVariable, otherNormalized.rootVariable))
    val cycleDetection = new collection.mutable.HashSet[(Set[V], Set[W])]
    def recurseAt(vs: Set[V], ws: Set[W]) {
      if (!(cycleDetection contains (vs, ws))) {
        cycleDetection.add((vs, ws))
        ((thisNormalized typesOf vs) intersect (otherNormalized typesOf ws)) foreach {
          a ⇒ leastCommonSubsumer addDescriptionAxiom ((vs, ws) Type a)
        }
        for {
          SomeV(r, xs) ← thisNormalized successorsOf vs
          SomeV(s, ys) ← otherNormalized successorsOf ws if (r equals s)
        } {
          leastCommonSubsumer addDescriptionAxiom ((vs, ws) Successor SomeV(r, (xs, ys)))
          recurseAt(xs, ys)
        }
        for {
          OnlyV(r, xs) ← thisNormalized successorsOf vs
          OnlyV(s, ys) ← otherNormalized successorsOf ws if (r equals s)
        } {
          leastCommonSubsumer addDescriptionAxiom ((vs, ws) Successor OnlyV(r, (xs, ys)))
          recurseAt(xs, ys)
        }
      }
    }
    recurseAt(thisNormalized.rootVariable, otherNormalized.rootVariable)
    leastCommonSubsumer
  }

  def asELsiClassExpression(): ELsiClassExpression[V] = {
    if (this.successors.values.flatten.exists({
      case OnlyV(_, _) ⇒ true
      case default    ⇒ false
    }))
      throw new IllegalArgumentException
    else
      this.asInstanceOf[ELsiClassExpression[V]]
  }

  // Members declared in java.lang.Comparable
  def compareTo(x$1: org.semanticweb.owlapi.model.OWLObject): Int = ???

  // Members declared in org.semanticweb.owlapi.model.HasAnnotationPropertiesInSignature
  def getAnnotationPropertiesInSignature(): java.util.Set[org.semanticweb.owlapi.model.OWLAnnotationProperty] = {
    Set().asJava
  }

  // Members declared in org.semanticweb.owlapi.model.HasAnonymousIndividuals
  def getAnonymousIndividuals(): java.util.Set[org.semanticweb.owlapi.model.OWLAnonymousIndividual] = {
    Set().asJava
  }

  // Members declared in org.semanticweb.owlapi.model.HasClassesInSignature
  def getClassesInSignature(): java.util.Set[OWLClass] = {
    getClassesInSignatureAsScala.asJava
  }

  protected def getClassesInSignatureAsScala(): Set[OWLClass] = {
    types.values.foldLeft[Set[OWLClass]](Set())(_ ++ _)
  }

  // Members declared in org.semanticweb.owlapi.model.HasContainsEntityInSignature
  def containsEntityInSignature(entity: org.semanticweb.owlapi.model.OWLEntity): Boolean = {
    if (entity.isOWLClass)
      getClassesInSignatureAsScala contains entity.asOWLClass
    else if (entity.isOWLObjectProperty)
      getObjectPropertiesInSignatureAsScala contains entity.asOWLObjectProperty
    else
      false
  }

  // Members declared in org.semanticweb.owlapi.model.HasDataPropertiesInSignature
  def getDataPropertiesInSignature(): java.util.Set[org.semanticweb.owlapi.model.OWLDataProperty] = {
    Set().asJava
  }

  // Members declared in org.semanticweb.owlapi.model.HasDatatypesInSignature
  def getDatatypesInSignature(): java.util.Set[org.semanticweb.owlapi.model.OWLDatatype] = {
    Set().asJava
  }

  // Members declared in org.semanticweb.owlapi.model.HasIndividualsInSignature
  def getIndividualsInSignature(): java.util.Set[org.semanticweb.owlapi.model.OWLNamedIndividual] = {
    Set().asJava
  }

  // Members declared in org.semanticweb.owlapi.model.HasObjectPropertiesInSignature
  def getObjectPropertiesInSignature(): java.util.Set[OWLObjectProperty] = {
    getObjectPropertiesInSignatureAsScala.asJava
  }

  protected def getObjectPropertiesInSignatureAsScala(): Set[OWLObjectProperty] = {
    successors.values.foldLeft[Set[OWLObjectProperty]](Set())(
      (outerObjectProperties, successors) ⇒
        outerObjectProperties ++ successors.foldLeft[Set[OWLObjectProperty]](Set())({
          case (innerObjectProperties, SomeV(r, _)) ⇒ innerObjectProperties + r
          case (innerObjectProperties, OnlyV(r, _)) ⇒ innerObjectProperties + r
        }))
  }

  // Members declared in org.semanticweb.owlapi.model.HasSignature
  def getSignature(): java.util.Set[OWLEntity] = {
    val signature: Set[OWLEntity] = getClassesInSignatureAsScala ++ getObjectPropertiesInSignatureAsScala
    signature.asJava
  }

  // Members declared in org.semanticweb.owlapi.model.OWLClassExpression
  def accept[O](x$1: org.semanticweb.owlapi.model.OWLClassExpressionVisitorEx[O]): O = ???
  def accept(x$1: org.semanticweb.owlapi.model.OWLClassExpressionVisitor): Unit = ???
  def asConjunctSet(): java.util.Set[org.semanticweb.owlapi.model.OWLClassExpression] = ???
  def asDisjunctSet(): java.util.Set[org.semanticweb.owlapi.model.OWLClassExpression] = ???
  def asOWLClass(): org.semanticweb.owlapi.model.OWLClass = ???
  def containsConjunct(x$1: org.semanticweb.owlapi.model.OWLClassExpression): Boolean = ???
  def getClassExpressionType(): org.semanticweb.owlapi.model.ClassExpressionType = ???
  def getComplementNNF(): org.semanticweb.owlapi.model.OWLClassExpression = ???
  def getNNF(): org.semanticweb.owlapi.model.OWLClassExpression = this
  def getObjectComplementOf(): org.semanticweb.owlapi.model.OWLClassExpression = ???
  def isAnonymous(): Boolean = false
  def isClassExpressionLiteral(): Boolean = ???

  def isOWLThing(): Boolean = {
    isOWLThing(rootVariable)
  }

  protected def isOWLThing(v: V): Boolean = {
    (typesOf(v) subsetOf Set(OWLThing)) &&
      (successorsOf(v) forall {
        case SomeV(_, _) ⇒ false
        case OnlyV(_, w) ⇒ isOWLThing(w)
      })
  }

  def isOWLNothing(): Boolean = {
    isOWLNothing(rootVariable)
  }

  protected def isOWLNothing(v: V): Boolean = {
    (typesOf(v) contains OWLNothing) ||
      (successorsOf(v) exists {
        case SomeV(_, w) ⇒ isOWLNothing(w)
        case OnlyV(_, _) ⇒ false
      })
  }

  // Members declared in org.semanticweb.owlapi.model.OWLObject
  def accept[O](x$1: org.semanticweb.owlapi.model.OWLObjectVisitorEx[O]): O = ???
  def accept(x$1: org.semanticweb.owlapi.model.OWLObjectVisitor): Unit = ???
  def getNestedClassExpressions(): java.util.Set[org.semanticweb.owlapi.model.OWLClassExpression] = ???
  def isBottomEntity(): Boolean = ???
  def isTopEntity(): Boolean = ???

}
