package users
import users.skiplist._

import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

package object utils {
  // True if right is n's right node
  def isRightOf(right: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    n match {
      case SkipNode(_, _, r, _) => r == right
    }
  }

  // True if down is n's down node
  def isDownOf(down: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    n match {
      case SkipNode(_, d, _, _) => d == down
    }
  }

  // True if lower can be reached by going only down from n
  def isLowerOf(lower: Node, n: Node): Boolean = {
    n match {
      case n@SkipNode(_, down, _, _) => n == lower || isLowerOf(lower, down)
      case Leaf => lower.isLeaf
    }
  }
  
  // True if n has a skipnode to the right
  def rightIsSkipNode(n: Node): Boolean = {
    require(n.isSkipNode)
    n match {
      case SkipNode(_, _, right, _) => {
        right.isSkipNode
      }
    }
  }

  def hasSameValue(a: Node, b: Node): Boolean = {
    (a,b) match {
      case (aS@SkipNode(vA,_,_,_),bS@SkipNode(vB,_,_,_)) => return vA == vB
      case _ => return false
    }
  }

  def hasSameHeight(a: Node, b: Node): Boolean = {
    (a,b) match {
      case (aS@SkipNode(_,_,_,vA),bS@SkipNode(_,_,_,vB)) => return vA == vB
      case _ => return false
    }
  }

  def hasValueAtLeast(a: Node, b: Node): Boolean = {
    (a,b) match {
      case (aS@SkipNode(vA,_,_,_),bS@SkipNode(vB,_,_,_)) => return vA >= vB
      case _ => return false
    }
  }
  
  def hasSameValueandHeight(a : Node, b : Node): Boolean = {
    hasSameHeight(a, b) && hasSameValue(a, b)
  }

  def rightNodeIsNot(n: Node, a: Node): Boolean = {
    n match {
      case SkipNode(_, _, right, _) => right != a
      case Leaf => false
    }
  }

  // TODO STOPPED HERE
  def lowerLevelIsStrictSuperset(n: Node, lower: Node): Boolean = {
    n match {
      case SkipNode(value, _, right, _) => {
        isInRightSubtree(value, lower) && lowerLevelIsStrictSuperset(right, lower)
      }
      case Leaf => true
    }
  }

  // True if 
  def isSubsetOf(n: Node, lower: Node): Boolean = {
    require(lower.isSkipNode)
    (n, lower) match {
      case (n@SkipNode(value, _, right, _), lower@SkipNode(valueL, _, _, _)) => {
        (lowerLevelIsStrictSuperset(n.right, lower) && value == valueL) || lowerLevelIsStrictSuperset(n, lower)
      }
      case (Leaf, _) => true
    }
  }

  def isInRightSubtree(target: Node, of: Node): Boolean = {
    (target, of) match {
      case (Leaf, Leaf) => false 
      case (Leaf, _) => true
      case (_, Leaf) => false
      case (SkipNode(_, _, _, _), SkipNode(_, _, rOf, _)) => {
        (target == rOf) || isInRightSubtree(target, rOf)
      }
    }
  }

  def isInRightSubtree(target: Int, of: Node): Boolean = {
    of match {
      case SkipNode(_, _, r@SkipNode(vRight, _, _, _), _) => {
        (target == vRight) || isInRightSubtree(target, r)
      }
      case _ => false
    }
  }


  // The node height, all the leaf are at height 0, skipnode at height l+1 where l is their height attribute
  def nodeHeight(n: Node): BigInt = {
    require(n.isSkipList)
    val nH: BigInt = n match {
      case SkipNode(_,d,_,h) => if (h == 0) {0} else {nodeHeight(d)+1} 
      case Leaf => 0
    }
    nH
  }.ensuring(res => res >= 0 && (n.isLeaf || n.hasHeight(res)))

  def size(t: Node): BigInt = {
    val s: BigInt = t match {
      case SkipNode(value, down, right, height) => 1 + size(down) + sizeRight(right)
      case Leaf => 0
    }
    s
  } ensuring (res => res >= 0)

  def sizeRight(t: Node): BigInt = {
    val sZ: BigInt = t match {
      case SkipNode(value, down, right, height) => 1 + sizeRight(right)
      case Leaf => 0
    }
    sZ
  } ensuring (res => res >= 0)

  // True n's right node is a subset of lower's right node
  def rightIsSubsetOfOtherRight(n: Node, lower: Node): Boolean = {
    require(n.isSkipNode)
    require(lower.isSkipNode)
    require(rightIsSkipNode(n))
    require(rightIsSkipNode(lower))
    (n, lower) match {
      case (n@SkipNode(_, down, right, _), lower@SkipNode(_, downL, rightL, _)) => {
        (right, rightL) match {
          case (right@SkipNode(_, _, _, _), rightL@SkipNode(_, _, _, _)) => {
            isSubsetOf(right, rightL)
          }
        }
      }
    }
  }

  def levelBelowContainsK(n: Node, k: Int): Boolean = {
    require(n.isSkipNode)
    n match {
      case n@SkipNode(_, down, _, _) => isInRightSubtree(k, down)
    }
  }

  def findNewDown(t: Node, v: Int): Node = t match {
    case SkipNode(value, down, right, height) => {
      if (value == v) {t}
      else {findNewDown(right, v)}
    }
    case Leaf => Leaf
  }

  def isInTheList(target: Int, of : Node): Boolean = of match {
    case SkipNode(value, down, right, height) => value == target || isInRightSubtree(target,of) || isInTheList(target,down)
    case Leaf => false
  }

  def isInTheList(target: Int, of: SkipList): Boolean = {
    return isInTheList(target,of.head)
  }

  //_____________________________________________ RIGHT AND DOWN

  def rightNodeHasValueLessThan(n: Node, v: Int): Boolean = {
    n match {
      case SkipNode(_, _, right, _) => right match {
        case SkipNode(value, _, _, _) => value < v
        case Leaf => false
      }
      case Leaf => false
    }
  }

  def isEqualOrInRightSubtree(target: Node, of: Node): Boolean = {
    return (target == of || isInRightSubtree(target,of))
  }

  def isEqualOrInRightSubtree(target: Int, of: Node): Boolean = {
    of match {
      case SkipNode(v,_,_,_) => (target == v || isInRightSubtree(target,of))
      case _ => false
    }
  }
  
  //_____________________________________________ SUBSET
  
  def levelLeftmost(t: Node, level: BigInt): Node = {
    require(t.isSkipList)
    require(t.hasValue(Int.MinValue))
    require(level >= 0)
    require(level <= nodeHeight(t))
    decreases(nodeHeight(t) - level)
    val res: Node = t match {
      case sn@SkipNode(value,down,_,height) =>
        assert(height >= level)
        if (height > level) {
          levelLeftmost(down, level)
        }
        else {
          assert(height == level)
          sn
        }
    }
    res
  } ensuring (res => res.isSkipList && res.hasValue(Int.MinValue) && res.hasHeight(level) && isLowerOf(res, t))
}