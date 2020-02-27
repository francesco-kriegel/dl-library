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

import com.google.common.collect.Sets
import collection.JavaConverters._
import scala.util.Random

import de.tudresden.inf.lat.dllibrary.Util._
import scala.concurrent.duration.Duration

object HSdagTest {

  def measure(code: ⇒ Unit): Duration = {
    val start = System.nanoTime
    code
    Duration.fromNanos(System.nanoTime - start)
  }

  def main(args: Array[String]) {
    (0 until 1000) foreach (n ⇒ {
      print("hypergraph " + n)
//      val hypergraph = randomHypergraph(Math.pow(Random.nextDouble() / 4, 2) + 0.1, (0 until 1 + Random.nextInt(12)).toSeq.toSet)
      val hypergraph = randomHypergraph(0.00001, (0 until 19).toSeq.toSet)
      println(" with " + hypergraph.size + " edges")
      println(hypergraph)
      val start = System.nanoTime
      val minimalHittingSets = HScartesian.allMinimalHittingSets(hypergraph)
      println("compute time: " + Duration.fromNanos(System.nanoTime - start).toSeconds + " s")
      //      println("naive result:  " + minimalHittingSets)
      //      println("test: " + minimalHittingSets.forall(isHittingSet(_, hypergraph)))
      val start2 = System.nanoTime
      val minimalHittingSets2 = HSdag.allMinimalHittingSets(hypergraph)
      println("compute time: " + Duration.fromNanos(System.nanoTime - start2).toSeconds + " s")
      //      println("HStree result: " + minimalHittingSets2)
      //      println("test: " + minimalHittingSets2.forall(isHittingSet(_, hypergraph)))
      //      if (!(minimalHittingSets subsetOf minimalHittingSets2))
      //        println("naive without HStree: " + (minimalHittingSets -- minimalHittingSets2))
      //      if (!(minimalHittingSets2 subsetOf minimalHittingSets))
      //        println("HStree without naive: " + (minimalHittingSets2 -- minimalHittingSets))
      println(minimalHittingSets equals minimalHittingSets2)
      if (!(minimalHittingSets equals minimalHittingSets2))
        throw new RuntimeException
      println()
      println()
      println()
    })
  }

  def randomHypergraph[A](density: Double, vertices: collection.Set[A]): collection.Set[collection.Set[A]] = {
    if (vertices.isEmpty) throw new IllegalArgumentException
    if (density equals 0) throw new IllegalArgumentException
    val result = (vertices.subsets filter { s ⇒ !s.isEmpty } filter { _ ⇒ Random.nextDouble() < density }).toSet
    if (!result.isEmpty)
      result
    else
      randomHypergraph(density, vertices)
  }

  def isHittingSet[A](candidate: collection.Set[A], hypergraph: collection.Set[collection.Set[A]]): Boolean = {
    hypergraph.forall(hyperedge ⇒ !(hyperedge intersect candidate).isEmpty)
  }

}

object HScartesian {

  def allMinimalHittingSets[A](hypergraph: collection.Set[collection.Set[A]]): collection.Set[collection.Set[A]] = {
//    val hittingSets: collection.Set[collection.Set[A]] = cartesianProduct(hypergraph)
//    var nonMinimalHittingSets: scala.collection.mutable.Set[collection.Set[A]] = Sets.newConcurrentHashSet().asScala
//    hittingSets.par.foreach(h1 ⇒
//      hittingSets.par.foreach(h2 ⇒
//        if (h1 strictSubsetOf h2)
//          nonMinimalHittingSets.add(h2)))
//    hittingSets -- nonMinimalHittingSets
    val hittingSets: collection.Set[collection.Set[A]] = cartesianProduct(hypergraph)
    var minimalHittingSets: scala.collection.mutable.Set[collection.Set[A]] = Sets.newConcurrentHashSet().asScala
    minimalHittingSets ++= hittingSets
    minimalHittingSets.par.foreach(h1 ⇒
      minimalHittingSets.par.foreach(h2 ⇒
        if (h1 strictSubsetOf h2)
          minimalHittingSets.remove(h2)))
    minimalHittingSets
  }

}

object HSdag {

  def allMinimalHittingSets[A](hypergraph: collection.Set[collection.Set[A]]): collection.Set[collection.Set[A]] = {
    allMinimalHittingSets(hypergraph.iterator)
  }

  def allMinimalHittingSets[A](hypergraph: Iterator[collection.Set[A]]): collection.Set[collection.Set[A]] = {
    val hstree = new HSdagPar[A](hypergraph)
    hstree.populate()
    hstree.allMinimalHittingSets()
  }

}

private class HSdagPar[A](F: Iterator[collection.Set[A]]) {

  private val seenHyperedges = new collection.mutable.HashSet[collection.Set[A]]

  private def hasNextHyperedge(): Boolean = {
    F.hasNext
  }

  private def getNextHyperedge(): collection.Set[A] = {
    val nextHyperedge = F.next()
    seenHyperedges.add(nextHyperedge)
    nextHyperedge
  }

  private def findHyperedge(condition: collection.Set[A] ⇒ Boolean): Option[collection.Set[A]] = {
    def scanF(): Option[collection.Set[A]] = {
      if (hasNextHyperedge) {
        val nextHyperedge = getNextHyperedge()
        if (condition(nextHyperedge))
          Some(nextHyperedge)
        else
          scanF()
      } else {
        None
      }
    }
    F.synchronized {
      (seenHyperedges find condition) orElse scanF()
    }
  }

  private def ignoreHyperedge(hyperedge: collection.Set[A]): Boolean = {
    seenHyperedges.remove(hyperedge)
  }

  sealed trait Label
  case class HyperedgeNode(hyperedge: collection.Set[A]) extends Label
  case class LeafNode() extends Label
  case class ClosedNode() extends Label
  case class NewNode() extends Label

  private class Node(
    var label: Label,
    val H:     collection.Set[A]) {

    val predecessors =
      new collection.mutable.HashMap[Node, collection.mutable.Set[A]] with collection.mutable.MultiMap[Node, A]
    val successors =
      new collection.mutable.HashMap[Node, collection.mutable.Set[A]] with collection.mutable.MultiMap[Node, A]

    def isNew(): Boolean = {
      label match {
        case NewNode() ⇒ true
        case default   ⇒ false
      }
    }

    def isLeaf(): Boolean = {
      label match {
        case LeafNode() ⇒ true
        case default    ⇒ false
      }
    }

    def isClosed(): Boolean = {
      label match {
        case ClosedNode() ⇒ true
        case default      ⇒ false
      }
    }

    def hyperedge(): Option[collection.Set[A]] = {
      label match {
        case HyperedgeNode(hyperedge) ⇒ Some(hyperedge)
        case default                  ⇒ None
      }
    }

    def ancestors(): collection.Set[Node] = {
      predecessors.keySet ++ predecessors.keySet.par.flatMap(_.ancestors)
    }

    def descendants(): collection.Set[Node] = {
      successors.keySet ++ successors.keySet.par.flatMap(_.descendants)
    }

  }

  private val rootNode: Node = new Node(new NewNode(), Set.empty[A])

  private def addEdge(source: Node, edgeLabel: A, target: Node): Unit = {
    source.successors.synchronized {
      source.successors.addBinding(target, edgeLabel)
    }
    target.predecessors.synchronized {
      target.predecessors.addBinding(source, edgeLabel)
    }
  }

  private def removeEdge(source: Node, edgeLabel: A, target: Node): Unit = {
    source.successors.synchronized {
      source.successors.removeBinding(target, edgeLabel)
    }
    target.predecessors.synchronized {
      target.predecessors.removeBinding(source, edgeLabel)
    }
  }

  private def removeNode(node: Node): Unit = {
    node.predecessors.foreachBinding((predecessor, edgeLabel) ⇒ removeEdge(predecessor, edgeLabel, node))
    node.successors.foreachBinding((successor, edgeLabel) ⇒ removeEdge(node, edgeLabel, successor))
  }

  private def activeNodes(): collection.Set[Node] = {
    rootNode.descendants
  }

  def allMinimalHittingSets(): collection.Set[collection.Set[A]] = {
    activeNodes filter { _.isLeaf } map { _.H }
  }

  def populate(): Unit = {
    expand(Set(rootNode))
  }

  private def expand(nodes: collection.Set[Node]): Unit = {
    val nextLevel = Sets.newConcurrentHashSet[Node]().asScala
    nodes.par.foreach(node ⇒ {
      if (activeNodes.par.exists(activeNode ⇒ activeNode.isLeaf && (activeNode.H strictSubsetOf node.H))) {
        node.label = new ClosedNode()
      } else {
        node.label =
          findHyperedge(hyperedge ⇒ (hyperedge intersect node.H).isEmpty)
            .map(hyperedge ⇒ { pruneWith(hyperedge); new HyperedgeNode(hyperedge) })
            .getOrElse(new LeafNode())
        node.hyperedge.foreach(hyperedge ⇒ {
          hyperedge.par.foreach(edgeLabel ⇒ {
            val successor =
              activeNodes.par.find(activeNode ⇒ activeNode.H equals (node.H + edgeLabel))
                .getOrElse(new Node(new NewNode(), node.H + edgeLabel))
            addEdge(node, edgeLabel, successor)
            if (successor.isNew)
              nextLevel.add(successor)
          })
        })
      }
    })
    if (!nextLevel.isEmpty)
      expand(nextLevel)
  }

  private def pruneWith(hyperedge: collection.Set[A]): Unit = {
    activeNodes.par.foreach(activeNode ⇒ {
      activeNode.label match {
        case HyperedgeNode(otherHyperedge) ⇒ {
          if (hyperedge strictSubsetOf otherHyperedge) {
            activeNode.label = new HyperedgeNode(hyperedge)
            val possiblyToBeRemoved = new collection.mutable.HashSet[Node]
            activeNode.successors.foreachBinding((successor, edgeLabel) ⇒ {
              if ((otherHyperedge -- hyperedge) contains edgeLabel) {
                removeEdge(activeNode, edgeLabel, successor)
                possiblyToBeRemoved += successor
                possiblyToBeRemoved ++= successor.descendants
              }
            })
            val certainlyToBeRemoved = fixedPoint[collection.mutable.HashSet[Node]](probablyToBeRemoved ⇒ {
              val moreProbablyToBeRemoved = probablyToBeRemoved.clone
              moreProbablyToBeRemoved.retain(node ⇒ node.predecessors.keySet subsetOf probablyToBeRemoved)
              moreProbablyToBeRemoved
            }, _ equals _)(possiblyToBeRemoved)
            certainlyToBeRemoved.par.foreach(node ⇒ removeNode(node))
            ignoreHyperedge(otherHyperedge)
          }
        }
        case default ⇒ {}
      }
    })
  }

}

private class HSdag2[A](F: Iterator[collection.Set[A]]) {

  private val seenHyperedges = new collection.mutable.HashSet[collection.Set[A]]

  private def hasNextHyperedge(): Boolean = {
    F.hasNext
  }

  private def getNextHyperedge(): collection.Set[A] = {
    val nextHyperedge = F.next()
    seenHyperedges.add(nextHyperedge)
    nextHyperedge
  }

  private def findHyperedge(condition: collection.Set[A] ⇒ Boolean): Option[collection.Set[A]] = {
    def scanF(): Option[collection.Set[A]] = {
      if (hasNextHyperedge) {
        val nextHyperedge = getNextHyperedge()
        if (condition(nextHyperedge))
          Some(nextHyperedge)
        else
          scanF()
      } else {
        None
      }
    }
    (seenHyperedges find condition) orElse scanF()
  }

  private def ignoreHyperedge(hyperedge: collection.Set[A]): Boolean = {
    seenHyperedges.remove(hyperedge)
  }

  sealed trait Label
  case class HyperedgeNode(hyperedge: collection.Set[A]) extends Label
  case class LeafNode() extends Label
  case class ClosedNode() extends Label
  case class NewNode() extends Label

  private class Node(
    var label: Label,
    val H:     collection.Set[A]) {

    val predecessors =
      new collection.mutable.HashMap[Node, collection.mutable.Set[A]] with collection.mutable.MultiMap[Node, A]
    val successors =
      new collection.mutable.HashMap[Node, collection.mutable.Set[A]] with collection.mutable.MultiMap[Node, A]

    def isNew(): Boolean = {
      label match {
        case NewNode() ⇒ true
        case default   ⇒ false
      }
    }

    def isLeaf(): Boolean = {
      label match {
        case LeafNode() ⇒ true
        case default    ⇒ false
      }
    }

    def isClosed(): Boolean = {
      label match {
        case ClosedNode() ⇒ true
        case default      ⇒ false
      }
    }

    def hyperedge(): Option[collection.Set[A]] = {
      label match {
        case HyperedgeNode(hyperedge) ⇒ Some(hyperedge)
        case default                  ⇒ None
      }
    }

    def ancestors(): collection.Set[Node] = {
      predecessors.keySet ++ predecessors.keySet.flatMap(_.ancestors)
    }

    def descendants(): collection.Set[Node] = {
      successors.keySet ++ successors.keySet.flatMap(_.descendants)
    }

  }

  private val rootNode: Node = new Node(new NewNode(), Set.empty[A])

  private def addEdge(source: Node, edgeLabel: A, target: Node): Unit = {
    source.successors.addBinding(target, edgeLabel)
    target.predecessors.addBinding(source, edgeLabel)
  }

  private def removeEdge(source: Node, edgeLabel: A, target: Node): Unit = {
    source.successors.removeBinding(target, edgeLabel)
    target.predecessors.removeBinding(source, edgeLabel)
  }

  private def removeNode(node: Node): Unit = {
    node.predecessors.foreachBinding((predecessor, edgeLabel) ⇒ removeEdge(predecessor, edgeLabel, node))
    node.successors.foreachBinding((successor, edgeLabel) ⇒ removeEdge(node, edgeLabel, successor))
  }

  private def activeNodes(): collection.Set[Node] = {
    rootNode.descendants
  }

  def allMinimalHittingSets(): collection.Set[collection.Set[A]] = {
    activeNodes filter { _.isLeaf } map { _.H }
  }

  def populate(): Unit = {
    expand(Set(rootNode))
  }

  private def expand(nodes: collection.Set[Node]): Unit = {
    val nextLevel = new collection.mutable.HashSet[Node]
    nodes.foreach(node ⇒ {
      if (activeNodes.exists(activeNode ⇒ activeNode.isLeaf && (activeNode.H strictSubsetOf node.H))) {
        node.label = new ClosedNode()
      } else {
        node.label =
          findHyperedge(hyperedge ⇒ (hyperedge intersect node.H).isEmpty)
            .map(hyperedge ⇒ { pruneWith(hyperedge); new HyperedgeNode(hyperedge) })
            .getOrElse(new LeafNode())
        node.hyperedge.foreach(hyperedge ⇒ {
          hyperedge.foreach(edgeLabel ⇒ {
            val successor =
              activeNodes.find(activeNode ⇒ activeNode.H equals (node.H + edgeLabel))
                .getOrElse(new Node(new NewNode(), node.H + edgeLabel))
            addEdge(node, edgeLabel, successor)
            if (successor.isNew)
              nextLevel.add(successor)
          })
        })
      }
    })
    if (!nextLevel.isEmpty)
      expand(nextLevel)
  }

  private def pruneWith(hyperedge: collection.Set[A]): Unit = {
    activeNodes.foreach(activeNode ⇒ {
      activeNode.label match {
        case HyperedgeNode(otherHyperedge) ⇒ {
          if (hyperedge strictSubsetOf otherHyperedge) {
            activeNode.label = new HyperedgeNode(hyperedge)
            val possiblyToBeRemoved = new collection.mutable.HashSet[Node]
            activeNode.successors.foreachBinding((successor, edgeLabel) ⇒ {
              if ((otherHyperedge -- hyperedge) contains edgeLabel) {
                removeEdge(activeNode, edgeLabel, successor)
                possiblyToBeRemoved += successor
                possiblyToBeRemoved ++= successor.descendants
              }
            })
            //            var changed = true
            //            while (changed) {
            //              changed = false
            //              val moreProbablyToBeRemoved = new collection.mutable.HashSet[Node]
            //              moreProbablyToBeRemoved ++= possiblyToBeRemoved
            //              moreProbablyToBeRemoved.retain(node ⇒ node.predecessors.keySet subsetOf possiblyToBeRemoved)
            //              changed = !(possiblyToBeRemoved equals moreProbablyToBeRemoved)
            //              possiblyToBeRemoved = moreProbablyToBeRemoved
            //            }
            //            possiblyToBeRemoved.foreach(node ⇒ removeNode(node))
            val certainlyToBeRemoved = fixedPoint[collection.mutable.HashSet[Node]](probablyToBeRemoved ⇒ {
              val moreProbablyToBeRemoved = probablyToBeRemoved.clone
              moreProbablyToBeRemoved.retain(node ⇒ node.predecessors.keySet subsetOf probablyToBeRemoved)
              moreProbablyToBeRemoved
            }, _ equals _)(possiblyToBeRemoved)
            certainlyToBeRemoved.foreach(node ⇒ removeNode(node))
            ignoreHyperedge(otherHyperedge)
          }
        }
        case default ⇒ {}
      }
    })
  }

}

private class HSdag[A](F: Iterator[collection.Set[A]]) {

  private class Node[A](
    var hyperedge: Option[collection.Set[A]],
    parent:        Option[(Node[A], A)]) {

    val parents = new collection.mutable.HashMap[Node[A], A]
    val children = new collection.mutable.HashMap[Node[A], A]
    val H = new collection.mutable.HashSet[A]
    private var _isClosed = false
    var _isLeaf = false

    if (parent.isDefined)
      parents put (parent.get._1, parent.get._2)

    def close() {
      _isClosed = true
      _isLeaf = false
      hyperedge = None
      children.clear()
    }

    def isClosed(): Boolean = {
      _isClosed
    }

    def isLeaf(): Boolean = {
      //      hyperedge.isEmpty && children.isEmpty && !isClosed
      _isLeaf
    }

    def ancestors(): collection.Set[Node[A]] = {
      // parents.map(_._1) ++ parents.flatMap(_._1.ancestors())
      val visitedNodes = new collection.mutable.HashSet[Node[A]]
      val ancestors = new collection.mutable.HashSet[Node[A]]
      def recurse(node: Node[A]) {
        if (visitedNodes.add(node)) {
          ancestors ++= node.parents.keys
          node.parents.keys foreach recurse
        }
      }
      recurse(this)
      ancestors
    }

    def descendants(): collection.Set[Node[A]] = {
      // children ++ children.flatMap(_.descendants())
      val visitedNodes = new collection.mutable.HashSet[Node[A]]
      val descendants = new collection.mutable.HashSet[Node[A]]
      def recurse(node: Node[A]) {
        if (visitedNodes.add(node)) {
          descendants ++= node.children.keys
          node.children.keys foreach recurse
        }
      }
      recurse(this)
      descendants
    }

    //    override def toString(): String = {
    //      toString(-4, "")
    //    }
    //
    //    private def toString(indent: Integer, text: String): String = {
    //      val prefix = (0 until indent).foldLeft[String]("")((s, _) ⇒ s + " ") + text
    //      if (isLeaf)
    //        prefix + "Leaf"
    //      else if (isClosed)
    //        prefix + "Closed"
    //      else
    //        prefix + "Node(" + hyperedge + ")" + children.foldLeft("")((s, n) ⇒ s + "\r\n" + n.toString(indent + 4, "|-" + n.parent.get._2 + "-"))
    //    }
  }

  private val seenHyperedges = new collection.mutable.HashSet[collection.Set[A]]

  private def hasNextHyperedge(): Boolean = {
    F.hasNext
  }

  private def getNextHyperedge(): collection.Set[A] = {
    val nextHyperedge = F.next()
    seenHyperedges.add(nextHyperedge)
    nextHyperedge
  }

  private def findHyperedge(condition: collection.Set[A] ⇒ Boolean): Option[collection.Set[A]] = {
    def scanF(): Option[collection.Set[A]] = {
      if (hasNextHyperedge) {
        val nextHyperedge = getNextHyperedge()
        if (condition(nextHyperedge))
          Some(nextHyperedge)
        else
          scanF()
      } else {
        None
      }
    }
    (seenHyperedges find condition) orElse scanF
  }

  private val rootNode =
    if (!hasNextHyperedge) new Node[A](None, None)
    else new Node[A](Some(getNextHyperedge()), None)

  private def allNodes(): collection.Set[Node[A]] = {
    allNodesBelow(rootNode)
  }

  private def allNodesBelow(node: Node[A]): collection.Set[Node[A]] = {
    Set(node) ++ (node.children.keys flatMap allNodesBelow)
  }

  private def leafNodes(): collection.Set[Node[A]] = {
    allNodes filter { _.isLeaf }
  }

  def populate() {
    expand(Set(rootNode))
  }

  private def expand(nodes: collection.Set[Node[A]]) {
    //    println("expanding " + nodes)
    //    println("current tree:")
    //    println(this)
    //    println()
    val nextLevel = new collection.mutable.HashSet[Node[A]]
    nodes foreach { node ⇒
      if (node.hyperedge.isDefined)
        node.hyperedge.get foreach (a ⇒ {
          val reusableNode = allNodes.find(someNode ⇒ H(someNode) equals H(node) + a)
          if (reusableNode.isDefined) {
            node.children.put(reusableNode.get, a)
            reusableNode.get.parents.put(node, a)
          } else {
            val successor = findHyperedge(someEdge ⇒ (someEdge intersect (H(node) + a)).isEmpty)
            val child = new Node[A](successor, Some((node, a)))
            child.H ++= H(node) + a
            child._isLeaf = !successor.isDefined
            if (successor.isDefined) { // pruning
              val hyperedge = successor.get
              var found = true
              while (found) {
                found = false
                allNodes.find(node ⇒ {
                  node.hyperedge.isDefined &&
                    (hyperedge subsetOf node.hyperedge.get) &&
                    !(node.hyperedge.get subsetOf hyperedge)
                }).foreach(node ⇒ {
                  found = true
                  seenHyperedges.remove(node.hyperedge.get)
                  node.hyperedge = Some(hyperedge)
                  val potentiallyToBeRemoved =
                    node.children.keySet
                      .filter(child ⇒ !(hyperedge contains node.children(child)))
                      .flatMap(child ⇒ Set(child) ++ child.descendants)
                  val reallyToBeRemoved =
                    potentiallyToBeRemoved.filter(node ⇒ {
                      node.parents.keySet subsetOf potentiallyToBeRemoved
                    })
                  node.children --= reallyToBeRemoved
                  reallyToBeRemoved foreach (n ⇒ {
                    n.close()
                    n.parents.keys foreach { parent ⇒ parent.children.remove(n) }
                    n.parents.clear()
                  })
                })
              }
              //                allNodes.filter(node ⇒ {
              //                  node.hyperedge.isDefined &&
              //                    (hyperedge subsetOf node.hyperedge.get) &&
              //                    !(node.hyperedge.get subsetOf hyperedge)
              //                }).foreach(node ⇒ {
              //                  seenHyperedges.remove(node.hyperedge.get)
              //                  node.hyperedge = Some(hyperedge)
              //                  val potentiallyToBeRemoved =
              //                    node.children.keySet
              //                      .filter(child ⇒ !(hyperedge intersect child.parents.values.toSet).isEmpty)
              //                      .flatMap(child ⇒ Set(child) ++ child.descendants)
              //                  val reallyToBeRemoved =
              //                    potentiallyToBeRemoved.filter(node ⇒ {
              //                      node.parents.keySet subsetOf potentiallyToBeRemoved
              //                    })
              //                  node.children --= reallyToBeRemoved
              //                  reallyToBeRemoved foreach { n ⇒ n.close(); n.parents.clear() }
              //                })
            }
            node.children.put(child, a)
            if (leafNodes.exists(leafNode ⇒ H(leafNode) subsetOf H(child)))
              child.close()
            if (!child.isClosed)
              nextLevel.add(child)
          }
        })
    }
    if (!nextLevel.isEmpty)
      expand(nextLevel)
  }

  private def H(node: Node[A]): collection.Set[A] = {
    //        if (!node.parents.isEmpty) {
    //          val parent = node.parents.head
    //          H(parent._1) + parent._2
    //        } else {
    //          Set()
    //        }
    node.H
    //    if (node equals rootNode) {
    //      Set()
    //    } else {
    //      val parent = node.parents.head
    //      H(parent._1) + parent._2
    //    }
  }

  def allMinimalHittingSets(): collection.Set[collection.Set[A]] = {
    leafNodes map H
  }

  override def toString(): String = {
    //    rootNode.toString()
    "HSdag with " + allNodes.size + " nodes and " + leafNodes.size + " leaf nodes"
  }

}
