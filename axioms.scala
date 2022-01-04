package users
import users.skiplist._
import users.utils._

import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

package object axioms {
  // True if the head has value Int.MinValue and has a height smaller than sl.maxHeight
  def headIsMinInt(sl: SkipList) = sl.head match {
    case Leaf => false
    case SkipNode(value, down, right, height) => (
      value == Int.MinValue && 
      sl.maxHeight >= 0 && 
      height <= sl.maxHeight
    )
  }
  
  // A node should never have a negative height. Recursive
  def hasNonNegativeHeight(node : Node): Boolean = {
    node match {
      case SkipNode(v,d,r,h) => h >= 0 && hasNonNegativeHeight(d) && hasNonNegativeHeight(r)
      case Leaf => true 
    }
  }

  // Given a node, if it is not at level 0, it should point to a node one level lower with the same value
  // If it is at level 0 already, it should point to a Leaf
  def heightDecreasesDown(node : Node): Boolean = {
    require(hasNonNegativeHeight(node))
    node match {
      case SkipNode(_,d,r,BigInt(0)) => d match {
        case Leaf => heightDecreasesDown(r)
        case SkipNode(_,_,_,_) => false
      }
      case SkipNode(v1,d,r,h1) => d match {
        case Leaf => false
        case SkipNode(v2,_,_,h2) => (h1-1 == h2) && (v1 == v2) && heightDecreasesDown(d) && heightDecreasesDown(r)
      }
      case Leaf => true
    }
  }

  // Given a node u, its right neighbour should have a value strictly greater than u's and the same height
  def increasesToTheRight(t: Node): Boolean = t match {
    case SkipNode(value, down, right, height) => right match {
      case SkipNode(valueR, _, _, heightR) => (
        height == heightR && 
        value < valueR && 
        increasesToTheRight(down) && 
        increasesToTheRight(right)
      )
      case Leaf => down match {
        case SkipNode(_, _, _, _) => increasesToTheRight(down)
        case Leaf => true
      }
    }
    case Leaf => true
  }

  def levelsAxiom(t: Node): Boolean = {
    t match {
      case SkipNode(value, down, right, height) => right match {
        case SkipNode(_, downR, _, _) => {
          if (down.isLeaf) {
            levelsAxiom(down) && levelsAxiom(right) && downR.isLeaf
          }
          else {
            levelsAxiom(down) && levelsAxiom(right) && isInRightSubtree(downR, down)
          }
        }
        case Leaf => levelsAxiom(down)
      }
      case Leaf => true
    }
  }

  // True if the given node represents a valid skiplist (no head condition)
  def isASkipList(t: Node): Boolean = {
    hasNonNegativeHeight(t) &&
    heightDecreasesDown(t) && 
    increasesToTheRight(t) && 
    levelsAxiom(t)
  }
  
  // True if the given Skiplist is valid given the previous axioms
  def isASkipList(sl: SkipList): Boolean = {
    headIsMinInt(sl) && 
    hasNonNegativeHeight(sl.head) && 
    heightDecreasesDown(sl.head) && 
    increasesToTheRight(sl.head) && 
    levelsAxiom(sl.head)
  }
}