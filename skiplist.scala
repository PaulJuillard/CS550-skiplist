import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

object SkipList {

/* file organization:

- Structure

- Implementation
  - search
  - insert
  - remove
  - size
  - isRight
  - utils
    - newdown

- Aux functions
  - struct
  - getters
  - right and down
  - size
  - subset

- Axioms
  - isSkipList
  - head is -inf
  - height > 0
  - height decreases down
  - increases to the right
  - levels

- Invariants
  0 - If sl is a skiplist and a is in the right subtree of node, then a.down is in the right subtree of node.down (and a.down.value == a.value) (kinda proved already)
  1 - If sl is a skiplist, insert(sl, a) is also a skiplist
  2 - If sl is a skiplist, remove(sl, a) is also a skiplist
  3 - If sl is a skiplist, insert(sl, a) contains a
  4 - If sl is a skiplist, remove(sl, a) does not contains a
  5 - If sl is a skiplist and b is in sl, insert(sl, a) contains b
  6 - If sl is a skiplist and b is in sl, remove(sl, a != b) contains b
  7 - If sl is a skiplist and a is in sl, search(sl, a) returns Some(a)
  8 - If sl is a skiplist and a is not in sl, search(sl, a) returns None

- Proofs and lemmas
  - in the same order
*/

//___________________________________________________________________________________________________________________________
//__________________________________________________________ DEV ______________________________________________________
//___________________________________________________________________________________________________________________________


//__________________________________________________________ Structure ______________________________________________________

sealed abstract class Node {
  def isSkipList = isASkipList(this)
  def isSkipNode = this match {case Leaf => false; case _ => true}
  def isLeaf: Boolean = !this.isSkipNode
  def hasValue(k: Int): Boolean = this match {case SkipNode(v, _, _, _) => v == k; case _ => false}
  def valueSmallerThan(k: Int): Boolean = this match {case SkipNode(v, _, _, _) => v < k; case _ => false}
  def valueAtMost(k: Int): Boolean = this match {case SkipNode(v, _, _, _) => v <= k; case _ => false}
  def valueHigherThan(k: Int): Boolean = this match {case SkipNode(v, _, _, _) => v > k; case _ => false}
  def heightAtMost(h: BigInt): Boolean = this match {case SkipNode(_, _, _, v) => v <= h; case _ => false}
  def heightAtLeast(h: BigInt): Boolean = this match {case SkipNode(_, _, _, v) => v >= h; case _ => false}
  def hasHeight(h: BigInt): Boolean = this match {case SkipNode(_, _, _, v) => v == h; case _ => false}
}
case class SkipList(head: Node, maxHeight: BigInt) {
  def isSkipList = isASkipList(this)
}
case class SkipNode(value: Int, down: Node, right: Node, height: BigInt) extends Node
case object Leaf extends Node

//__________________________________________________________ Implementation ______________________________________________________

//_____________________________________________ SEARCH

  def search_(t: Node, target: Int): Option[Int] = t match {
    case SkipNode(v,d,r,_) =>
        if (v == target) { 
          Some(v) 
        }
        else {
          r match {
            case SkipNode(vR,_,_,_) => 
              if (vR <= target) { // If value is somewhere to the right, go right
                search_(r, target)
              }
              else { // If not, try down
                search_(d, target)
              }
            case Leaf => search_(d, target) // Reached the end of this level, go down
          }
        }
    case Leaf => None()

  }
  def search(sl: SkipList, target: Int): Option[Int] = {
    search_(sl.head, target)
  }

  //_____________________________________________ INSERT

  // def insert(t: Node, k: Int, insertHeight: Int): Node = {
  //   require(isSkipList(t))
  //   require(insertHeight >= 0)
  //   decreases(size(t))
  //   t match { // Returns the list with k inserted
  //     case sn@SkipNode(value, down, right, height) => {
  //       if (height > insertHeight) { // We are too high, recurse on lower level
  //         lem_sizeDecreasesDown(sn)
  //         lem_elementOfSkipListIsSkipList(sn)
  //         SkipNode(value, insert(down, k, insertHeight), right, height)
  //       }
  //       else { //at correct level, insert lower, then insert right
  //         lem_sizeDecreasesDown(sn)
  //         val lowerLeftmostNode = insert(down, k, insertHeight)
  //         assert(isRight(lowerLeftmostNode, k))
  //         assert(isSkipList(lowerLeftmostNode))
         
  //         insertRight(t, k, lowerLeftmostNode) //insert right need new underlying level to update links to down nodes
  //       }
  //     }
  //     case Leaf => Leaf // Found a leaf (we are at level -1)
  //   }
  // }

  def insertUpwards(k: Int, desiredHeight: BigInt, topLeftmost: Node, currentLeftmost: Node, currentLevel: BigInt, lowerLeftmost: Node): Node = {
    // insertRight in levels 0 to maxHeight
    // if desiredHeight is lower than level, simply updates links to the new subtree
    require(topLeftmost.isSkipList)
    require(lowerLeftmost.isSkipList)
    require(currentLeftmost.isSkipList)
    require(topLeftmost.isSkipNode)
    require(currentLeftmost.isSkipNode)
    require(topLeftmost.hasValue(Int.MinValue))
    require(desiredHeight >= 0)
    require(currentLevel <= nodeHeight(topLeftmost))
    require(desiredHeight <= nodeHeight(topLeftmost))
    require(currentLevel >= 0)
    require(currentLevel >= (desiredHeight + 1) || isInRightSubtree(k, lowerLeftmost))
    require(k > Int.MinValue)
    require(nodeHeight(currentLeftmost) == currentLevel)
    require(isLowerOf(currentLeftmost, topLeftmost))
    require(currentLevel == 0 || 
      (lowerLeftmost.isSkipNode && isSubsetOf(currentLeftmost, lowerLeftmost) && (nodeHeight(lowerLeftmost) + 1 == currentLevel)))
    decreases(nodeHeight(topLeftmost) + 1 - currentLevel)

    lem_isLowerOfImpliesSameValue(currentLeftmost, topLeftmost)
    if (nodeHeight(topLeftmost) == 0) { // Only one insert to do, at level 0
      val finalCurrentLeftmost = currentLeftmost match {
        case currentLeftmost@SkipNode(value, _, _, _) => {
          lem_insertRightZeroHeightContainsK(currentLeftmost, k)
          lem_insertRightZeroHeightIsSkipList(currentLeftmost, k)
          insertRightZeroHeight(currentLeftmost, k)
        }
      }
      finalCurrentLeftmost
    }
    else if (currentLevel == nodeHeight(topLeftmost)) { // Last insert, don't recurse upwards
      //plug lower level
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      //insert right
      if (currentLevel > desiredHeight) {
        updatedCurrentLeftmost
      }
      else {
        val finalCurrentLeftmost = updatedCurrentLeftmost match {
          case updatedCurrentLeftmost@SkipNode(_, _, _, _) => {
            plugLowerLevelReturnsSkipList(currentLeftmost, lowerLeftmost)
            insertRight(updatedCurrentLeftmost, k)
          }
        }
        finalCurrentLeftmost
      }
    }
    else if (currentLevel == 0) { // Insert at level 0 and recurse upwards
      val finalCurrentLeftmost = currentLeftmost match {
        case currentLeftmost@SkipNode(value, _, _, _) => {
          lem_isLowerOfImpliesSameValue(currentLeftmost, topLeftmost)
          lem_insertRightZeroHeightContainsK(currentLeftmost, k)
          lem_insertRightZeroHeightIsSkipList(currentLeftmost, k)
          insertRightZeroHeight(currentLeftmost, k)
        }
      }
      val nextCurrentLeftmost = levelLeftmost(topLeftmost, currentLevel+1)
      lem_isDownOf(topLeftmost, nextCurrentLeftmost, currentLeftmost, currentLevel)
      lem_isDownOfImpliesSubset(currentLeftmost, nextCurrentLeftmost)
      lem_insertRightZeroHeightReturnsSuperset(currentLeftmost, k)
      lem_isSubsetOfTransitivity(nextCurrentLeftmost, currentLeftmost, finalCurrentLeftmost)
      insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, finalCurrentLeftmost)
    }
    else if (currentLevel <= desiredHeight) { // Insert at current level and recurse upwards
      //plug lower level
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      //insert right
      val finalCurrentLeftmost = updatedCurrentLeftmost match {
        case updatedCurrentLeftmost@SkipNode(_, _, _, _) => {
          plugLowerLevelReturnsSkipList(currentLeftmost, lowerLeftmost)
          lem_plugLowerLevelContainsKBelow(currentLeftmost, lowerLeftmost, k)
          insertRight(updatedCurrentLeftmost, k)
        }
      }
      //insert up
      val nextCurrentLeftmost = levelLeftmost(topLeftmost, currentLevel+1)
      lem_isDownOf(topLeftmost, nextCurrentLeftmost, currentLeftmost, currentLevel)
      lem_isDownOfImpliesSubset(currentLeftmost, nextCurrentLeftmost)
      lem_plugLowerLevelReturnsSuperset(currentLeftmost, lowerLeftmost)
      lem_insertRightReturnsSuperset(updatedCurrentLeftmost, k)
      lem_isSubsetOfTransitivity(nextCurrentLeftmost, currentLeftmost, updatedCurrentLeftmost)
      lem_isSubsetOfTransitivity(nextCurrentLeftmost, updatedCurrentLeftmost, finalCurrentLeftmost)
      lem_insertRightContainsKey(updatedCurrentLeftmost, k)
      lem_insertRightReturnsSkipList(updatedCurrentLeftmost, k)
      insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, finalCurrentLeftmost)
    }
    else { // plug and recurse upwards
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      val nextCurrentLeftmost = levelLeftmost(topLeftmost, currentLevel+1)
      plugLowerLevelReturnsSkipList(currentLeftmost, lowerLeftmost)
      lem_isDownOf(topLeftmost, nextCurrentLeftmost, currentLeftmost, currentLevel)
      lem_isDownOfImpliesSubset(currentLeftmost, nextCurrentLeftmost)
      lem_plugLowerLevelReturnsSuperset(currentLeftmost, lowerLeftmost)
      lem_isSubsetOfTransitivity(nextCurrentLeftmost, currentLeftmost, updatedCurrentLeftmost)
      insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, updatedCurrentLeftmost)
    }
  }

  def lem_insertRightReturnsSuperset(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueSmallerThan(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        r match {
          case r@SkipNode(valueR, downR, rightR, heightR) => {
            if (valueR <= k) {
              if (valueR == k) {
                lem_isSubsetOfItself(n, r)
              }
              else {
                sizeDecreasesToTheRight(n)
                lem_insertRightReturnsSuperset(r, k)
                lem_rightIsSubsetOfOtherRightImpliesSubset(n, insertedRight)
                check(isSubsetOf(n, insertedRight))
              }
            }
            else {
              val nD = findNewDown(d, k)
              val nR = SkipNode(k, nD, r, h)
              assert(isSubsetOf(r, nR)) // TODO : Proof (true because r is nr's right, so nr is strict superset of r)
              lem_rightIsSubsetOfOtherRightImpliesSubset(n, insertedRight)
              check(isSubsetOf(n, insertedRight))
            }
          }
          case Leaf => ()
        }
      }
    }
    isSubsetOf(n, insertRight(n, k))
  }.holds

  def lem_rightIsSubsetOfOtherRightImpliesSubset(n: Node, lower: Node): Boolean = {
    require(n.isSkipNode)
    require(lower.isSkipNode)
    require(rightIsSkipNode(n))
    require(rightIsSkipNode(lower))
    require(hasSameValue(n, lower))
    require(rightIsSubsetOfOtherRightAndSameDown(n, lower))
    (n, lower) match {
      case (n@SkipNode(_, down, right, _), lower@SkipNode(_, downL, rightL, _)) => {
        (right, rightL) match {
          case (right@SkipNode(_, _, _, _), rightL@SkipNode(_, _, _, _)) => {
            assert(isSubsetOf(right, rightL))
          }
        }
      }
    }
    isSubsetOf(n, lower) // TODO : Proof
  }.holds

  def rightIsSubsetOfOtherRightAndSameDown(n: Node, lower: Node): Boolean = {
    require(n.isSkipNode)
    require(lower.isSkipNode)
    require(rightIsSkipNode(n))
    require(rightIsSkipNode(lower))
    (n, lower) match {
      case (n@SkipNode(_, down, right, _), lower@SkipNode(_, downL, rightL, _)) => {
        (right, rightL) match {
          case (right@SkipNode(_, _, _, _), rightL@SkipNode(_, _, _, _)) => {
            isSubsetOf(right, rightL) && down == downL
          }
        }
      }
    }
  }

  def rightIsSkipNode(n: Node): Boolean = {
    require(n.isSkipNode)
    n match {
      case SkipNode(_, _, right, _) => {
        right.isSkipNode
      }
    }
  }

  def lem_isSubsetOfItself(n: Node, right: Node): Boolean = {
    require(n.isSkipNode)
    require(right.isSkipNode)
    require(n.isSkipList)
    require(isRightOf(right, n))
    n match {
      case SkipNode(_, _, right, _) => {
        lem_toTheRightIsStrictSubset(right, n)
      }
    }
    isSubsetOf(n, n)
  }.holds

  def lem_insertRightZeroHeightReturnsSuperset(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(n.hasHeight(0))
    n match {
      case n@SkipNode(_, _, _, _) => {
        assume(isSubsetOf(n, insertRightZeroHeight(n, k))) // TODO : Proof
        isSubsetOf(n, insertRightZeroHeight(n, k))
      }
    }
  }.holds

  def isDownOf(down: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    n match {
      case SkipNode(_, d, _, _) => d == down
    }
  }

  def isRightOf(right: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    n match {
      case SkipNode(_, _, r, _) => r == right
    }
  }

  def lem_isDownOfImpliesSubset(down: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    require(down.isSkipNode)
    require(n.isSkipList)
    require(isDownOf(down, n))
    decreases(size(n))
    (n, down) match {
      case (n@SkipNode(value, _, right, _), SkipNode(valueL, _, _, _)) => {
        check(value == valueL)
        right match {
          case right@SkipNode(valueR, downR, _, _) => {
            sizeDecreasesToTheRight(n)
            lem_isDownOfImpliesSubset(downR, right)
            lem_isInRightSubtreeImpliesSubset(downR, down)
            lem_isSubsetOfTransitivity(right, downR, down)
          }
          case Leaf => ()
        }
      }
    }
    isSubsetOf(n, down)
  }.holds

  def lem_isInRightSubtreeImpliesSubset(right: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    require(right.isSkipNode)
    require(n.isSkipList)
    require(isInRightSubtree(right, n))
    (n, right) match {
      case (SkipNode(value, _, r, _), right@SkipNode(_, _, _, _)) => {
        if (right != r) {
          lem_isInRightSubtreeImpliesSubset(right, r)
          lem_toTheRightIsSubset(r, n)
          lem_isSubsetOfTransitivity(right, r, n)
        }
        else {
          lem_toTheRightIsSubset(r, n)
        }
      }
    }
    isSubsetOf(right, n)
  }.holds

  def lem_toTheRightIsSubset(right: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    require(right.isSkipNode)
    require(n.isSkipList)
    require(isRightOf(right, n))
    (n, right) match {
      case (SkipNode(_, _, _, _), right@SkipNode(valueR, _, rightR, _)) => {
        lem_toTheRightIsStrictSubset(right, n)
      }
    }
    isSubsetOf(right, n)
  }.holds

  def lem_toTheRightIsStrictSubset(right: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    require(right.isSkipNode)
    require(n.isSkipList)
    require(isInRightSubtree(right, n))
    (n, right) match {
      case (n@SkipNode(_, _, _, _), right@SkipNode(valueR, _, rightR, _)) => {
        lem_isInRightSubtreeImpliesValueIsAlsoIn(n, right, valueR)
        rightR match {
          case SkipNode(_, _, _, _) => {
            lem_rightIsAlsoInRightSubtree(n, right)
            lem_toTheRightIsStrictSubset(rightR, n)
          }
          case Leaf => ()
        }
      }
    }
    lowerLevelIsStrictSuperset(right, n)
  }.holds

  def lem_plugLowerLevelReturnsSuperset(currentLeftmost: Node, lowerLeftmost: Node): Boolean = {
    require(currentLeftmost.isSkipNode)
    require(lowerLeftmost.isSkipNode)
    require(currentLeftmost.isSkipList)
    require(lowerLeftmost.isSkipList)
    require(isSubsetOf(currentLeftmost, lowerLeftmost))
    require(nodeHeight(currentLeftmost) > 0)
    require(nodeHeight(currentLeftmost) == nodeHeight(lowerLeftmost) + 1)
    assume(isSubsetOf(currentLeftmost, plugLowerLevel(currentLeftmost, lowerLeftmost))) // TODO : Proof
    isSubsetOf(currentLeftmost, plugLowerLevel(currentLeftmost, lowerLeftmost))
  }.holds
  
  def lem_isDownOf(n: Node, down1: Node, down2: Node, height: BigInt): Boolean = {
    require(n.isSkipNode)
    require(n.isSkipList)
    require(down1.hasHeight(height+1))
    require(down2.hasHeight(height))
    require(isLowerOf(down1, n))
    require(isLowerOf(down2, n))
    n match {
      case n@SkipNode(_, down, _, _) => {
        lem_isLowerOfImplyHeightAtLeast(n, down1, height+1)
        check(n != down2)
        if (n == down1) {
          lem_isLowerOfAndSameHeightImplySame(down, down2, height)
        }
        else {
          lem_isDownOf(down, down1, down2, height)
        }
      }
    }
    isDownOf(down2, down1)
  }.holds

  def lem_isLowerOfImplyHeightAtLeast(n: Node, lower: Node, height: BigInt): Boolean = {
    require(n.isSkipNode)
    require(n.isSkipList)
    require(lower.hasHeight(height))
    require(isLowerOf(lower, n))
    n match {
      case SkipNode(_, down, _, _) => {
        if (n != lower) {
          lem_isLowerOfImplyHeightAtLeast(down, lower, height)
        }
      }
    }
    n.heightAtLeast(height)
  }.holds

  def lem_isLowerOfAndSameHeightImplySame(n: Node, lower: Node, height: BigInt): Boolean = {
    require(n.isSkipList)
    require(lower.hasHeight(height))
    require(n.hasHeight(height))
    require(isLowerOf(lower, n))
    n match {
      case SkipNode(_, down, _, _) => {
        down match {
          case down@SkipNode(_, _, _, _) => {
            lem_isLowerOfImpliesSkiplist(n, lower)
            lem_greaterHeightImpliesNotLower(down, lower, height-1)
          }
          case Leaf => ()
        }
      }
    }
    lower == n
  }.holds

  def lem_isLowerOfImpliesSkiplist(n: Node, lower: Node): Boolean = {
    require(n.isSkipList)
    require(isLowerOf(lower, n))
    n match {
      case SkipNode(_, down, _, _) => {
        if (n != lower) {
          lem_isLowerOfImpliesSkiplist(down, lower)
        }
      }
      case Leaf => ()
    }
    lower.isSkipList
  }.holds

  def lem_greaterHeightImpliesNotLower(n: Node, lower: Node, height: BigInt): Boolean = {
    require(n.isSkipList)
    require(lower.isSkipList)
    require(lower.heightAtLeast(height+1))
    require(n.hasHeight(height))
    n match {
      case SkipNode(_, down, _, _) => {
        down match {
          case SkipNode(_, _, _, _) => {
            lem_greaterHeightImpliesNotLower(down, lower, height-1)
          }
          case Leaf => ()
        }
      }
    }
    !isLowerOf(lower, n)
  }.holds

  def lem_isSubsetOfTransitivity(a: Node, b: Node, c: Node): Boolean = {
    require(a.isSkipNode)
    require(b.isSkipNode)
    require(c.isSkipNode)
    require(a.isSkipList)
    require(b.isSkipList)
    require(c.isSkipList)
    require(isSubsetOf(a, b))
    require(isSubsetOf(b, c))
    
    (a,b,c) match {
      case (an@SkipNode(a_v,_,a_r,_), bn@SkipNode(b_v, _,b_r,_), cn@SkipNode(c_v, _,c_r,_)) =>
        
        a_r match {
          case a_r@SkipNode(_,_,_,_) => 
            lem_isSubsetOfTransitivity(a_r, b, c)
          case Leaf =>
        }
        assert(isSubsetOf(a_r, c))
        //        if(a_v != c_v) assert(isInRightSubtree(a_v, cn))
        lem_valueOfSubsetIsInSuperset(a_v, an, bn)
        lem_valueOfSubsetIsInSuperset(a_v, bn, cn)
        if(a_v == c_v) {
          assert(isSubsetOf(a_r, cn))
          a_r match{
            case a_r@SkipNode(v,_,_,_) => 
              lem_elementOfSkipListIsSkipList(an)
              assume(a_r.isSkipList)
              //lem_valueAtRightIsHigher(an, a_r) //TODO easy precond
              lem_inRightSubtreeImpliesDifference(an, a_r)
              assume(v != c_v) //TODO but above should be enough
          }
          assert(lowerLevelIsStrictSuperset(a_r, cn))
          assert(isSubsetOf(a, c))
        }
        else {
          assert(isSubsetOf(a_r, c))
          a_r match{
            case a_r@SkipNode(v,_,_,_) => 
              lem_elementOfSkipListIsSkipList(an)
              lem_valueAtRightIsHigher(an, a_r)
              assume(v != c_v) //TODO but above should be enough
              assert(lowerLevelIsStrictSuperset(a_r, cn))
            case Leaf => 
              assert(lowerLevelIsStrictSuperset(a_r, cn))

          }

          assert(isInRightSubtree(a_v, c)) // from lem_valueOfSubsetIsInSuperset(a_v, bn, cn)
          assume(lowerLevelIsStrictSuperset(a_r, cn)) //TODO but proved above
          assert(lowerLevelIsStrictSuperset(a, cn)) // the 2 above imply this
          assert(isSubsetOf(a, c))
        }
      case (Leaf, _, _) => 
      case _ => ()
    }
    isSubsetOf(a,c)
  }.holds
  
  def lem_valueOfSubsetIsInSuperset(v: Int, sub: SkipNode, sup: SkipNode): Unit = {
    require(sub.isSkipNode)
    require(sup.isSkipNode)
    require(isSubsetOf(sub, sup))
    require(sub.value == v || isInRightSubtree(v, sub))

    if(sub.value != v){
      assert(isInRightSubtree(v, sub))
      lem_subsetRightIsSubset(sub, sup)
      sub.right match {
        case sn@SkipNode(_,_,_,_) => lem_valueOfSubsetIsInSuperset(v, sn, sup)
      }
    }

  } ensuring ( _ => isInRightSubtree(v, sup) || sup.value == v)

  def lem_subsetRightIsSubset(sub: SkipNode, sup: Node): Unit = {
    require(sup.isSkipNode)
    require(sub.isSkipNode)
    require(isSubsetOf(sub, sup))
  } ensuring ( _ => isSubsetOf(sub.right, sup))

  def lem_insertRightReturnsSkipList(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v != k) {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR < k) {
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightReturnsSkipList(r, k)
              }
              else {
                lem_newDownReturnsSkipList(d, k)
                lem_insertRightPreservesLevelsAxiom(n, k)
                lem_insertRightPreservesHeightAxiom(n, k)
                assert(increasesToTheRight(insertedRight))
                check(insertedRight.isSkipList)
              }
            }
            case Leaf => {
              lem_newDownReturnsSkipList(d, k)
              lem_insertRightPreservesHeightAxiom(n, k)
              lem_insertRightPreservesLevelsAxiom(n, k)
              check(insertedRight.isSkipList)
            }
          }
        }
      }
    }
    insertRight(n, k).isSkipList
  }.holds

  def lem_insertRightPreservesLevelsAxiom(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v != k) {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR < k) {
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightPreservesLevelsAxiom(r, k)
              }
              else if (valueR > k) {
                lem_newDownReturnsSkipList(d, k)
                val nD = findNewDown(d, k)
                val nR = SkipNode(k, nD, r, h)
                if (!d.isLeaf) {
                  lem_newDownReturnsSkipNodeOfValue(d, k)
                  lem_newDownIsInRightSubtreeOfOld(d, k)
                  check(isInRightSubtree(downR, d))
                  lem_bothInRightSubtreeWithLowerValue(d, nD, downR, k, valueR)
                  assert(isInRightSubtree(downR, nD))
                }
                check(levelsAxiom(insertedRight))
              }
            }
            case Leaf => {
              lem_newDownReturnsSkipList(d, k)
              if (!d.isLeaf) {
                lem_newDownIsInRightSubtreeOfOld(d, k)
              }
              check(levelsAxiom(insertedRight))
            }
          }
        }
      }
    }
    levelsAxiom(insertedRight)
  }.holds

  def lem_insertRightPreservesHeightAxiom(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    lem_insertRightPreservesPositiveHeightAxiom(n, k)
    assert(insertedRight.heightAtLeast(BigInt(1)))
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v != k) {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR < k) {
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightPreservesHeightAxiom(r, k)
              }
              else {
                lem_newDownReturnsSkipList(d, k)
                val nD = findNewDown(d, k)
                val nR = SkipNode(k, nD, r, h)
                lem_newDownReturnsSkipNodeOfValue(d, k)
              }
            }
            case Leaf => {
              lem_newDownReturnsSkipList(d, k)
              val nD = findNewDown(d, k)
              val nR = SkipNode(k, nD, r, h)
              lem_newDownReturnsSkipNodeOfValue(d, k)
            }
          }
        }
      }
    }
    heightDecreasesDown(insertedRight)
  }.holds

  def lem_insertRightPreservesPositiveHeightAxiom(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v != k) {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR < k) {
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightPreservesPositiveHeightAxiom(r, k)
              }
              else {
                lem_newDownReturnsSkipList(d, k)
              }
            }
            case Leaf => {
              lem_newDownReturnsSkipList(d, k)
            }
          }
        }
      }
    }
    hasNonNegativeHeight(insertedRight)
  }.holds

  def lem_findNewDownHasGivenHeightAndValue(t: Node, v: Int): Boolean = {
    require(t.isSkipList)
    require(findNewDown(t, v).isSkipNode)
    t match {
      case SkipNode(value, down, right, height) => {
        if (value != v) {
          lem_findNewDownHasGivenHeightAndValue(right, v)
        }
      }
    }
    findNewDown(t, v).hasValue(v) && hasSameHeight(findNewDown(t, v), t)
  }.holds

  def lem_insertRightContainsKey(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueSmallerThan(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        r match {
          case r@SkipNode(valueR, downR, rightR, heightR) => {
            if (valueR <= k) {
              sizeDecreasesToTheRight(n)
              higherLevelIsSubsetofLowerOne(n, r)
              if (valueR != k) {
                assert(r.down.valueSmallerThan(k))
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                val nR = insertRight(r, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightContainsKey(r, k)
                (nR, insertedRight) match {
                  case (nR@SkipNode(_, _, _, _), insertedRight@SkipNode(_, _, _, _)) => {
                    lem_isInRightSubtreeTransitive(insertedRight, nR, k)
                  }
                }
              }
            }
          }
          case Leaf => ()
        }
      }
    }
    isInRightSubtree(k, insertedRight)
  }.holds

  def lem_plugLowerLevelContainsKBelow(oldCurrentLeftmost: Node, newLowerLeftmost: Node, k: Int): Boolean = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(isInRightSubtree(k, newLowerLeftmost))
    decreases(sizeRight(oldCurrentLeftmost))
    assume(levelBelowContainsK(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost), k)) // TODO : Proof
    levelBelowContainsK(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost), k)
  }.holds

  def levelBelowContainsK(n: Node, k: Int): Boolean = {
    require(n.isSkipNode)
    n match {
      case n@SkipNode(_, down, _, _) => isInRightSubtree(k, down)
    }
  }

  def plugLowerLevel(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Node = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    decreases(sizeRight(oldCurrentLeftmost))

    (oldCurrentLeftmost, newLowerLeftmost) match {
      case (oldCurrentLeftmost@SkipNode(value, down, right, height), newLowerLeftmost@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(newLowerLeftmost, value)
        right match {
          case right@SkipNode(valueR, _, _, _) => {
            if (value != valueL) {
              lem_newDownReturnsSkipList(newLowerLeftmost, value)
              lem_isInRightSubtreeImpliesSelfValueIsLower(newLowerLeftmost, value)
              lem_newDownReturnsSkipNodeOfValue(newLowerLeftmost, value)
              lem_newDownIsInRightSubtreeOfOld(newLowerLeftmost, value)
              lem_inRightSubtreeHasSameNodeHeight(newLowerLeftmost, newDown)
              lem_toTheRightIsStillSuperset(newLowerLeftmost, newDown, right, valueR)
              assert(isSubsetOf(right, newDown))
            }
            assert(isSubsetOf(right, newDown))
            SkipNode(value, newDown, plugLowerLevel(right, newDown), height)
          }
          case Leaf => SkipNode(value, newDown, Leaf, height)
        }
      }
    }
  }

  // Note : lowerLeftmost is the new node under t with inserted value k
  // we need to update all links
  def insertRight(n: Node, k: Int): Node = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v == k) {n}
        else {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR <= k) {
                sizeDecreasesToTheRight(n)
                higherLevelIsSubsetofLowerOne(n, r)
                if (valueR == k) {
                  n
                }
                else {
                  assert(r.down.valueSmallerThan(k))
                  lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                  val newRight = insertRight(r, k)
                  SkipNode(v, d, newRight, h)
                }
              }
              else {
                val newDown = findNewDown(d, k)
                val newRight = SkipNode(k, newDown, r, h)
                SkipNode(v, d, newRight, h)
              }
            }
            case Leaf => {
              val newDown = findNewDown(d, k)
              val newRight = SkipNode(k, newDown, Leaf, h)
              SkipNode(v, d, newRight, h)
            }
          }
        }
      }
    }
  }
  
  def insertRightZeroHeight(n: SkipNode, k: Int): Node = {
    require(n.isSkipList)
    require(n.value <= k)
    require(nodeHeight(n) == 0)
    decreases(size(n))
    if (n.value == k) {n}
    else {
      n.right match {
        case r@SkipNode(valueR, downR, rightR, heightR) => {
          if (valueR <= k) {
            sizeDecreasesToTheRight(n)
            val newRight = insertRightZeroHeight(r, k)
            SkipNode(n.value, n.down, newRight, n.height)
          }
          else {
            val newRight = SkipNode(k, Leaf, n.right, n.height) 
            SkipNode(n.value, n.down, newRight, n.height)
          }
        }
        case Leaf => {
          val newRight = SkipNode(k, Leaf, Leaf, n.height)
          SkipNode(n.value, n.down, newRight, n.height)
        }
      }
    }
  }

  // boil node up to level newHeight
  def increaseHeight(n: Node, newHeight:BigInt): Node = {
    require(n.isSkipList)
    require(newHeight >= nodeHeight(n))
    decreases(newHeight - nodeHeight(n))
    n match {
      case n@SkipNode(value, down, right, height) => {
        if (height >= newHeight) {
          n
        } 
        else {
          increaseHeight(SkipNode(value, n, Leaf, height+1), newHeight)
        }
      }
      case Leaf => Leaf
    }
  }

  // def insert(sl: SkipList, k: Int, height: BigInt): SkipList = {
  //   require(isSkipList(sl))
  //   require(height >= 0)
  //   // if needed, bring first value to same height
  //   val newHead = increaseHeight(sl.head, height)
  //   assert(isSkipList(newHead))
  //   SkipList(insertUpwards(k, height, newHead, 0, Leaf), max(sl.maxHeight, height))
  // } 

  // def insert(sl: SkipList, k:BigInt): SkipList = {
  //    if (isIn(sl, k)) {
  //      sl
  //    }
  //    def getRandomLevel(rd: Random, acc:BigInt):BigInt = {if (rd.nextInt(2) == 0) {acc} else {getRandomLevel(rd, acc+1)}}
  //    val r = new Random
  //    val height = getRandomLevel(r, 0)
  //    //println("random height : " + height)
  //    insert(sl, k, height)
  // }

//_____________________________________________ REMOVE


  // def remove(sl: SkipList, k:BigInt): SkipList = {
  //   require(isSkipList(sl))
  //   require(k !=BigInt.MinValue)
  //   SkipList(remove(sl.head, k), sl.maxHeight)
  // }

  // def remove(t: Node, k:BigInt): Node = {
  //   require(isSkipList(t))
  //   decreases(size(t))
  //   t match { // Returns the list with k removed
  //     case t@SkipNode(value, down, right, height) => {
  //       lem_sizeDecreasesDown(t)
  //       val lowerLeftmostNode = remove(down, k)
  //       //removeReturnsSkipList(down, k)
  //       // assert(isSkipList(lowerLeftmostNode))
  //       removeRight(t, k, lowerLeftmostNode)
  //     }
  //     case Leaf => Leaf // Found a leaf (we are at level -1)
  //   }
  // }
  
  // def removeRight(t: Node, k:BigInt, lowerLevel: Node): Node = {
  //   require(isSkipList(t))
  //   require(isSkipList(lowerLevel))
  //   decreases(size(t))
  //   t match {
  //     case t@SkipNode(value, down, right, height) => {
  //       val newDown = findNewDown(lowerLevel, value)
  //       lem_newDownReturnsSkipList(lowerLevel, value)
  //       right match {
  //         case SkipNode(valueR, downR, rightR, heightR) => {
  //           if (valueR == k) { // Remove right
  //             assert(isInRightSubtree(rightR, t))
  //             lem_sizeAtRightIsLower(t, rightR)
  //             SkipNode(value, newDown, removeRight(rightR, k, newDown), height)
  //           }
  //           else { // Value is not the next node, just recurse to the right
  //             sizeDecreasesToTheRight(t)
  //             SkipNode(value, newDown, removeRight(right, k, newDown), height)
  //           }
  //         }
  //         case Leaf => SkipNode(value, newDown, Leaf, height) // Reached end of this level, just update lower node
  //       }
  //     }
  //     case Leaf => Leaf
  //   }
  // }

//_____________________________________________ IS RIGHT

  // Return true when a node target is in the subtree of a node of
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

//_____________________________________________ UTILS
def findNewDown(t: Node, v: Int): Node = t match {
  case SkipNode(value, down, right, height) => 
    if (value == v) {t}
    else {findNewDown(right, v)}
    case Leaf => Leaf
}
  
//__________________________________________________________AXIOMS______________________________________________________

  // Return true when the given Skiplist is indeed a skiplist given the previous axioms
  def isASkipList(sl: SkipList): Boolean = {
    headIsMinInt(sl) && 
    hasNonNegativeHeight(sl.head) && 
    heightDecreasesDown(sl.head) && 
    increasesToTheRight(sl.head) && 
    levelsAxiom(sl.head)
  }

  // Return true when the given node represent a skiplist (exept for the head condition)
  def isASkipList(t: Node): Boolean = {
    hasNonNegativeHeight(t) &&
    heightDecreasesDown(t) && 
    increasesToTheRight(t) && 
    levelsAxiom(t)
  }

  // Return true when the head of the given skiplist has theBigInt.MinValue value and has a height smaller than the max height
  def headIsMinInt(sl: SkipList) = sl.head match {
    case Leaf => false
    case SkipNode(value, down, right, height) => (
      value == Int.MinValue && 
      sl.maxHeight >= 0 && 
      height == sl.maxHeight
    )
  }
  
  // A node should never have a negative height
  def hasNonNegativeHeight(node : Node): Boolean = {
    node match {
      case SkipNode(v,d,r,h) => h >= 0 && hasNonNegativeHeight(d) && hasNonNegativeHeight(r)
      case Leaf => true 
    }
  }

  // Given a node, if it is not at level 0, it should points on itself with a level_l = level_h-1
  // If it is at level 0 already, its child should be a Leaf
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
  
  //_________________________________________________ OTHER STRUCTURAL PROPERTIES __________________________________________
  // NOTE many of these were moved out of context and need requires to be general

  //_____________________________________________ GETTERS
  def isInTheList(target: Int, of : Node): Boolean = of match {
    case SkipNode(value, down, right, height) => isInRightSubtree(target,of) || isInTheList(target,down)
    case Leaf => false
  }

  def isInTheList(target: Int, of: SkipList): Boolean = {
    return isInRightSubtree(target,of.head)
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

  //_____________________________________________ SIZE
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

  //_____________________________________________ RIGHT AND DOWN

  def isLowerOf(lower: Node, n: Node): Boolean = {
    n match {
      case n@SkipNode(_, down, _, _) => n == lower || isLowerOf(lower, down)
      case Leaf => lower.isLeaf
    }
  }

  def rightNodeHasValueLessThan(n: Node, v: Int): Boolean = {
    n match {
      case SkipNode(_, _, right, _) => right match {
        case SkipNode(value, _, _, _) => value < v
        case Leaf => false
      }
      case Leaf => false
    }
  }

  def rightNodeIsNot(n: Node, a: Node): Boolean = {
    n match {
      case SkipNode(_, _, right, _) => right != a
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

  def lowerLevelIsStrictSuperset(n: Node, lower: Node): Boolean = {
    n match {
      case SkipNode(value, _, right, _) => {
        isInRightSubtree(value, lower) && lowerLevelIsStrictSuperset(right, lower)
      }
      case Leaf => true
    }
  }

  def isSubsetOf(n: Node, lower: Node): Boolean = {
    require(lower.isSkipNode)
    (n, lower) match {
      case (n@SkipNode(value, _, right, _), lower@SkipNode(valueL, _, _, _)) => {
        (lowerLevelIsStrictSuperset(n.right, lower) && value == valueL) || lowerLevelIsStrictSuperset(n, lower)
      }
      case (Leaf, _) => true
    }
  }

  

  //_________________________________________________INVARIANTS DOC __________________________________________
  // Invariants : 
  // If sl is skiplist and insert element then result is also skiplist and search returns Some(x)
  // If search element in the list, it is found x
  // If remove then search, not found x
  // If isSkipList, every level is a subset of the level below
  // Search is probabilistically log : tr0 dur j'ai peur 

  // New propositions : Splitting some properties, and define the notion of "being in the list"
  // Def - Element is in the list if it is in the right subtree of first element, or in the list of element just below
  // 0 - If sl is a skiplist and a is in the right subtree of node, then a.down is in the right subtree of node.down (and a.down.value == a.value) (kinda proved already)
  // 1 - If sl is a skiplist, insert(sl, a) is also a skiplist
  // 2 - If sl is a skiplist, remove(sl, a) is also a skiplist
  // 3 - If sl is a skiplist, insert(sl, a) contains a
  // 4 - If sl is a skiplist, remove(sl, a) does not contains a
  // 5 - If sl is a skiplist and b is in sl, insert(sl, a) contains b
  // 6 - If sl is a skiplist and b is in sl, remove(sl, a != b) contains b
  // 7 - If sl is a skiplist and a is in sl, search(sl, a) returns Some(a)
  // 8 - If sl is a skiplist and a is not in sl, search(sl, a) returns None
  
  //_________________________________________________________INVARIANTS____________________________________________________
  
  // 0 - If sl is a skiplist and a is in the right subtree of node, then a.down is in the right subtree of node.down (and a.down.value == a.value) (kinda proved already)
  def higherLevelIsSubsetofLowerOne(n: SkipNode, x: SkipNode): Unit = {
    require(n.isSkipList)
    require(x.isSkipList)
    require(isInRightSubtree(x, n))
    if (n.right != x) {
      n.right match {
        case r@SkipNode(_, _, _, _) => {
          higherLevelIsSubsetofLowerOne(r, x)
          (n.down, r.down, x.down) match {
            case (nD@SkipNode(_, _, _, _), rD@SkipNode(_, _, _, _), xD@SkipNode(_, _, _, _)) => lem_isInRightSubtreeTransitive(nD, rD, xD)
            case _ => ()
          }
        }
      }
    }
  } ensuring (_ => (n.down.isLeaf && x.down.isLeaf) || isInRightSubtree(x.down, n.down))

  def higherLevelIsSubsetofLowerOne(v: Int, n: SkipNode): Unit = {
    require(n.isSkipList)
    require(isInRightSubtree(v, n))
    assert(n.right.isSkipNode)
    n.right match {
      case r@SkipNode(valueR, downR, _, _) => {
        if (v != valueR) {
          higherLevelIsSubsetofLowerOne(v, r)
          if (n.down.isSkipNode) {
            (r.down, n.down) match {
              case (rD@SkipNode(_, _, _, _), nD@SkipNode(_, _, _, _)) => lem_isInRightSubtreeTransitive(nD, rD, v)
            }
          }
        }
        else {
          if (n.down.isSkipNode) {
            (r.down, n.down) match {
              case (rD@SkipNode(valueRD, _, _, _), nD@SkipNode(_, _, _, _)) => lem_isInRightSubtreeImpliesValueIsAlsoIn(nD, rD, valueRD)
            }
          }
        }
      }
    }
  } ensuring (_ => n.down.isLeaf || isInRightSubtree(v, n.down))

/*  
   1 - If sl is a skiplist, insert(sl, a) is also a skiplist ==============
  def insertReturnsSkiplist(sl : SkipList, v:BigInt, height:BigInt): Unit = {
    require(isSkipList(sl))
    require(height>=0)
    
  } ensuring (_ => isSkipList(insert(sl,v,height)))

  def insertReturnsSkiplist(n : Node, v:BigInt, height:BigInt): Unit = {
    require(isSkipList(n))
    require(height>=0)
    
  } ensuring (_ => isSkipList(insert(n,v,height)))
  
  // 2 - If sl is a skiplist, remove(sl, a) is also a skiplist ==============
  def insertReturnsSkiplist(sl : SkipList, v:BigInt): Unit = {
    require(isSkipList(sl))
    
  } ensuring (_ => isSkipList(remove(sl,v)))

  def insertReturnsSkiplist(n : Node, v:BigInt): Unit = {
    require(isSkipList(n))
    
  } ensuring (_ => isSkipList(remove(n,v)))

  // 3 - If sl is a skiplist, insert(sl, a) contains a ======================
  def insertReallyInserts(sl: SkipList, v:BigInt, height:BigInt): Unit = {
    require(isSkipList(sl))
    require(height>=0)
  } ensuring (_ => isInTheList(v,insert(sl,v,height)))

  def insertReallyInserts(n: Node, v:BigInt, height:BigInt): Unit = {
    require(isSkipList(n))
    require(height>=0)
  } ensuring (_ => isInTheList(v,insert(n,v,height)))

  // 4 - If sl is a skiplist, remove(sl, a) does not contains a =============
  def removeReallyRemoves(sl: SkipList, v:BigInt): Unit = {
    require(isSkipList(sl))
  } ensuring (_ => !isInTheList(v,remove(sl,v)))

  def removeReallyRemoves(n: Node, v:BigInt): Unit = {
    require(isSkipList(n))
  } ensuring (_ => !isInTheList(v,remove(n,v)))

  // 5 - If sl is a skiplist and b is in sl, insert(sl, a) contains b =======
  def insertDoesNotRemoveElements(sl: SkipList, a:BigInt, height:BigInt, b:BigInt): Unit = {
    require(isSkipList(sl))
    require(height>=0)
    require(isInTheList(b,sl))
  } ensuring (_ => isInTheList(b,insert(sl,a,height)))

  def insertDoesNotRemoveElements(n: Node, a:BigInt, height:BigInt, b:BigInt): Unit = {
    require(isSkipList(n))
    require(height>=0)
    require(isInTheList(b,n))
  } ensuring (_ => isInTheList(b,insert(n,a,height)))

  // 6 - If sl is a skiplist and b is in sl, remove(sl, a != b) contains b ===
  def removeDoesNotRemoveOtherElements(sl: SkipList, a:BigInt, b:BigInt): Unit = {
    require(isSkipList(sl))
    require(isInTheList(b,sl))
  } ensuring (_ => isInTheList(b,remove(sl,a)))
  
  def removeDoesNotRemoveOtherElements(n: Node, a:BigInt, b:BigInt): Unit = {
    require(isSkipList(n))
    require(isInTheList(b,n))
  } ensuring (_ => isInTheList(b,remove(n,a)))

  // 7 - If sl is a skiplist and a is in sl, search(sl, a) returns Some(a) ===
    def searchFindsElement(sl: SkipList, v:BigInt): Unit = {
      require(isSkipList(sl))
      require(isInTheList(v,sl))
    } ensuring (_ => search(sl,v) == Some(v))

  def searchFindsElement(n: Node, v:Int): Unit = {
    require(isSkipList(n))
    require(isInTheList(v,n))  
    n match {
      case Leaf => ()
      case SkipNode(value, down, right, height) => {
        if (value == v){
          ()
        }
        else if(isInRightSubtree(v, right)){
          assert(isInRightSubtree(v, right))
          decreases(sizeRight(n))
          searchFindsElement(right, v)
          //assume(nodeForIntInRightSubtree(v,n)!= None())
        } else {
          assume(isInTheList(v,down))
          assume(search_(n,v) == Some(v))

        }
      }
    }
  } ensuring (_ => search_(n,v) == Some(v))
  
  // 8 - If sl is a skiplist and a is not in sl, search(sl, a) returns None ==
  def searchFindsNone(sl: SkipList, v:BigInt): Unit = {
    require(isSkipList(sl))
    require(!isInTheList(v,sl))
  } ensuring (_ => search(sl,v) == None())

  def searchFindsNone(n: Node, v:BigInt): Unit = {
    require(isSkipList(n))
    require(!isInTheList(v,n))
    n match {
      case Leaf => ()
      case SkipNode(value, down, right, height) => {
        assert(value != v)
        assert(!isInRightSubtree(v, right))
        assume(!isInTheList(v,right))
          searchFindsNone(down,v)
          searchFindsNone(right,v)
      }
    }
  } ensuring (_ => search(n,v) == None())
*/

//___________________________________________________________________________________________________________________________
//__________________________________________________________ PROOFS and lemmas ______________________________________________________
//___________________________________________________________________________________________________________________________

  @extern
  def assume(b: Boolean): Unit = {
    (??? : Unit)
  } ensuring (_ => b)


  // not categorized 
   def lem_elementOfSkipListIsSkipList(t: SkipNode): Unit = { // Is not used in proofs, but keep it there to make sure we don't break SkipList axioms
    require(t.isSkipList)
    assert(levelsAxiom(t.down))
    assert(levelsAxiom(t.right))
  } ensuring (_ => t.down.isSkipList && t.right.isSkipList)

  def lem_valueAtRightIsHigher(n: SkipNode, r: SkipNode): Unit = {
    require(n.isSkipList)
    require(r.isSkipList)
    require(isInRightSubtree(r, n))
    n.right match {
      case Leaf => ()
      case rN@SkipNode(value, down, right, height) => 
        if (rN != r){
          lem_valueAtRightIsHigher(rN,r)
        }
    }
  } ensuring (_ => n.value<r.value)

  def lem_valueAtRightIsHigher(n: SkipNode, r: Int): Unit = {
    require(n.isSkipList)
    require(isInRightSubtree(r, n))
    n.right match {
      case Leaf => ()
      case rN@SkipNode(value, down, right, height) => 
        if (rN.value != r){
          lem_valueAtRightIsHigher(rN,r)
        }
    }
  } ensuring (_ => n.value<r)

  def lem_isLowerOfImpliesSameValue(lower: Node, n: Node): Unit = {
    require(n.isSkipList)
    require(isLowerOf(lower, n))
    n match {
      case n@SkipNode(v, d, r, _) => if (n != lower) {lem_isLowerOfImpliesSameValue(lower, d)}
      case Leaf => ()
    }
  } ensuring (_ => lower.isLeaf || hasSameValue(n, lower))

  //_____________________________________________ INSERT PROOF

  def lem_skipnodeToTheRightAlsoHasKeyToTheRight(n: Node, r: Node, v: Int): Unit = {
    require(n.isSkipNode)
    require(r.valueSmallerThan(v))
    require(n.isSkipList)
    require(r.isSkipList)
    require(isInRightSubtree(r, n))
    require(isInRightSubtree(v, n))
    decreases(sizeRight(n))
    n match {
      case sN@SkipNode(value, down, right, height) => {
        right match{
          case sR@SkipNode(_, _, _, _) => {
            if (sR != r){
              r match {
                case skipR@SkipNode(_,_,_,_) => {
                  lem_valueAtRightIsHigher(sR,skipR)
                  lem_skipnodeToTheRightAlsoHasKeyToTheRight(sR,skipR,v)
                }
              }
            }
          }
        }
      }
    }
  } ensuring (_ => isInRightSubtree(v, r))


  def lem_toTheRightIsStillSuperset(newLowerLeftmost: Node, newDown: Node, n: Node, v: Int): Unit = {
    require(n.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(lowerLevelIsStrictSuperset(n, newLowerLeftmost))
    require(isInRightSubtree(newDown, newLowerLeftmost))
    require(n.hasValue(v))
    require(newDown.valueSmallerThan(v))
    decreases(size(n))
    (newDown, n) match {
      case (newDown@SkipNode(value, down, right, height), n@SkipNode(valueN, _, rightN, _)) => {
        lem_isInRightSubtreeInequality(newLowerLeftmost, newDown, valueN)
        sizeDecreasesToTheRight(n)
        rightN match {
          case rightN@SkipNode(valueR, _, _, _) =>  lem_toTheRightIsStillSuperset(newLowerLeftmost, newDown, rightN, valueR)
          case Leaf => ()
        }
      }
    }
  } ensuring (_ => isSubsetOf(n, newDown))

  def lem_higherRootHasLowerValue(n: Node, lower: Node): Unit = {
    require(n.isSkipNode)
    require(lower.isSkipNode)
    require(n.isSkipList)
    require(lower.isSkipList)
    require(nodeHeight(n) > 0)
    require(nodeHeight(lower)+1 == nodeHeight(n))
    require(isSubsetOf(n,lower))
    (n, lower) match {
      case (high@SkipNode(value, down, right, _), low@SkipNode(valueL, _, _, _)) => {
        if(value!=valueL){
          assert(lowerLevelIsStrictSuperset(high, lower))
          down match {
            case d@SkipNode(vD, _, _, _) => {
              assert(value==vD)
              assert(isInRightSubtree(vD, low))
              lem_valueAtRightIsHigher(low,vD)
            }
          }
        }
      }
    }
  } ensuring (_ => hasValueAtLeast(n, lower))
  
  def lem_newDownIsInRightSubtreeOfOld(n: Node, k: Int): Unit = {
    require(n.isSkipList)
    require(n.valueSmallerThan(k))
    decreases(sizeRight(n))
    (findNewDown(n, k), n) match {
      case (SkipNode(value, down, right, height), n@SkipNode(_, _, rightN, _)) => {
        rightN match {
          case SkipNode(valueR, _, _, _) => {
            if (valueR < k) {
              lem_newDownIsInRightSubtreeOfOld(rightN, k)
            }
            else if (valueR > k) {
              lem_newDownWithTooHighKeyNodeReturnsLeaf(rightN, k)
            }
          }
          case Leaf => ()
        }
      }
      case (Leaf, _) => ()
    }
  } ensuring (_ => isInRightSubtree(findNewDown(n, k), n))

  def lem_insertRightZeroHeightIsSkipList(n: SkipNode, k: Int) : Unit = {
    require(n.isSkipList)
    require(n.value <= k)
    require(nodeHeight(n) == 0)

    if (n.value != k) {
      n.right match {
        case r@SkipNode(valueR, downR, rightR, heightR) => {
          if (valueR <= k) {
            sizeDecreasesToTheRight(n)
            lem_insertRightZeroHeightIsSkipList(r, k)
          }
        }
        case Leaf => {
          val newRight = SkipNode(k, Leaf, Leaf, n.height)
          val ret = SkipNode(n.value, n.down, newRight, n.height)
          check(levelsAxiom(newRight))
          check(levelsAxiom(ret))
        }
      }
    }
  } ensuring ( _ => insertRightZeroHeight(n, k).isSkipList)

  def lem_insertRightZeroHeightContainsK(n: SkipNode, k: Int) : Unit = {
    require(n.isSkipList)
    require(n.value < k)
    require(nodeHeight(n) == 0)
    n.right match {
      case r@SkipNode(valueR, downR, rightR, heightR) => {
        if (valueR < k) {
          sizeDecreasesToTheRight(n)
          lem_insertRightZeroHeightContainsK(r, k)
        }
      }
      case Leaf => ()
    }
  } ensuring ( _ => isInRightSubtree(k,insertRightZeroHeight(n, k)))


  def hasSameValueandHeight(a : Node, b : Node): Boolean = {
      (a,b) match {
      case (SkipNode(vA,dA,rA,hA), SkipNode(vB,dB,rB,hB)) => vA == vA && hA == hA
      case (Leaf, Leaf) => true
      case _ => false
    }
  }
  
  def plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Unit = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    decreases(sizeRight(oldCurrentLeftmost))
    (oldCurrentLeftmost, newLowerLeftmost) match {
      case (o@SkipNode(value, down, right, height), n@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(n, value)
        assert(plugLowerLevel(o,n).isSkipNode)
        assert(hasSameValueandHeight(plugLowerLevel(o,n),o))
        right match {
          case right@SkipNode(valueR, _, _, _) => plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(right,newDown)
          case Leaf => lem_newDownReturnsSkipList(newLowerLeftmost, value)
        }
      }
    }
  } ensuring (hasNonNegativeHeight(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)) && increasesToTheRight(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)))

  def plugLowerLevelReturnsHeightDrecreasesDown(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Unit = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    decreases(sizeRight(oldCurrentLeftmost))
    (oldCurrentLeftmost, newLowerLeftmost) match {
      case (o@SkipNode(value, down, right, height), n@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(n, value)
        assert(plugLowerLevel(o,n).isSkipNode)
        assert(hasSameValueandHeight(plugLowerLevel(o,n),o))
        right match {
          case right@SkipNode(valueR, _, _, _) => {
            plugLowerLevelReturnsHeightDrecreasesDown(right,newDown)
            plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(o,n)
          }
          case Leaf => {
            if (value != valueL){
              lem_newDownReturnsSkipList(n, value)
              lem_isInRightSubtreeImpliesSelfValueIsLower(n, value)
              lem_newDownReturnsSkipNodeOfValue(n,value)
              plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(o,n)
              assert(heightDecreasesDown(newDown))
              newDown match {
                case nD@SkipNode(ndV, ndD, ndR, ndH) => {
                  assert(ndV == value)
                  lem_newDownIsInRightSubtreeOfOld(n,value)
                  lem_inRightSubtreeHasSameNodeHeight(n, nD)
                  assert(height == heightL+1)
                  assert(ndH == heightL)
                }
              }
            }
          }
        }
      }
    }
  } ensuring (heightDecreasesDown(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)))


  def plugLowerLevelReturnsLevelsAxiom(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Unit = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    decreases(sizeRight(oldCurrentLeftmost))
    (oldCurrentLeftmost, newLowerLeftmost) match {
      case (o@SkipNode(value, down, right, height), n@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(n, value)
        assert(plugLowerLevel(o,n).isSkipNode)
        assert(hasSameValueandHeight(plugLowerLevel(o,n),o))
        right match {
          case right@SkipNode(valueR, downR, _, _) => {
            plugLowerLevelReturnsLevelsAxiom(right,newDown)
            lem_newDownIsInRightSubtreeOfOld(newDown,valueR)
            assert(isInRightSubtree(findNewDown(newDown, valueR), newDown))
          }
          case Leaf => lem_newDownReturnsSkipList(newLowerLeftmost, value)
        }
      }
    }
  } ensuring (levelsAxiom(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)))

  def plugLowerLevelReturnsSkipList(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Unit = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    (oldCurrentLeftmost,newLowerLeftmost) match {
      case (o@SkipNode(vO,dO,rO,hO), n@SkipNode(vN,dN,rN,hN)) => {
        plugLowerLevel(o,n) match {
          case p@SkipNode(vP, dP, rP, hP) => {
            plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(o,n)
            plugLowerLevelReturnsLevelsAxiom(o,n)
            plugLowerLevelReturnsHeightDrecreasesDown(o,n)
            assert(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost).isSkipList)
          }
        }
      }
    }
  } ensuring (plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost).isSkipList)

  

//_____________________________________________ SIZE proof and lemmas

  def lem_sizeSkipNodeIsPositive(t: SkipNode): Unit = {
  } ensuring (_ => size(t) > 0)

  def sizeDecreasesToTheRight(n: SkipNode): Unit = {
    require(n.isSkipList)
    lem_sizeAtRightIsLower(n, n.right)
    n.right match {
      case SkipNode(_, _, _, _) => assert(size(n) > size(n.right))
      case Leaf => {
        lem_sizeSkipNodeIsPositive(n)
      }
    }
  } ensuring (_ => size(n) > size(n.right))

  def lem_sizeDecreasesDown(n: SkipNode): Unit = {
  } ensuring (_ => size(n) > size(n.down))

  def lem_sizeAtRightIsLower(n: Node, x: Node): Unit = {
    require(n.isSkipList)
    require(x.isSkipList)
    require(isInRightSubtree(x, n))
    decreases(nodeHeight(n))
    n match {
      case n@SkipNode(_, down, right, _) => x match {
        case x@SkipNode(_, downR, rightR, _) => {
          lem_inRightSubtreeImpliesLowerMeasure(n, x)
          higherLevelIsSubsetofLowerOne(n, x)
          down match {
            case (down@SkipNode(_, _, _, _)) => {
              lem_sizeAtRightIsLower(down, downR)
              lem_sizeSkipNodeIsPositive(down)
            }
            case Leaf => ()
          }
        }
        case Leaf => ()
      }
      case Leaf => ()
    }
  } ensuring (_ => n.isLeaf || size(n) > size(x))
  
  def lem_inRightSubtreeImpliesLowerMeasure(n: Node, x: Node): Boolean = {
    require(isInRightSubtree(x, n))
    decreases(sizeRight(n))
    n match {
      case n@SkipNode(value, down, right, height) => {
        if (x != right) {
          x match {
            case x@SkipNode(_, _, _, _) => {
              lem_inRightSubtreeImpliesLowerMeasure(right, x)
            }
            case Leaf => ()
          }
        }
      }
    }
    sizeRight(n) > sizeRight(x)
  }.holds

  def lem_bothInRightSubtreeWithLowerValue(n: Node, a: Node, b: Node, v1: Int, v2: Int): Boolean = {
    require(n.isSkipList)
    require(a.hasValue(v1))
    require(b.hasValue(v2))
    require(v1 < v2)
    require(isInRightSubtree(a, n))
    require(isInRightSubtree(b, n))
    n match {
      case SkipNode(_, _, right, _) => {
        if (right != a) {
          lem_isInRightSubtreeImpliesValueIsAlsoIn(n, b, v2)
          lem_rightSubtreeDoesNotSkipValues(n, a, v2)
          lem_bothInRightSubtreeWithLowerValue(right, a, b, v1, v2)
        }
      }
    }
    isInRightSubtree(b, a)
  }.holds

 //_____________________________________________ IS RIGHT proof and lemmas

  // Proof of isInRightSubtree transitivity : Lemmas that didn't even need to be proven :
  // If x is in n's right subtree and n.down is not a Leaf, then x.down is not a Leaf
  // If x is in n's right subtree then n is not a Leaf
  def lem_rightIsAlsoInRightSubtree(n: SkipNode, x: SkipNode): Unit = {
    require(isInRightSubtree(x, n))
    n.right match {
      case Leaf => ()
      case r@SkipNode(value, down, right, height) => {
        if (r != x) {
          lem_rightIsAlsoInRightSubtree(r, x)
        } 
      }
    }
  } ensuring (_ => isInRightSubtree(x.right, n))

  def lem_isInRightSubtreeTransitive(n1: SkipNode, n2: SkipNode, n3: SkipNode): Unit = {
    require(isInRightSubtree(n2, n1))
    require(isInRightSubtree(n3, n2))
    if (n3 != n2.right) {
      lem_rightIsAlsoInRightSubtree(n1, n2)
      n2.right match {
        case n2R@SkipNode(_, _, _, _) => {
          lem_isInRightSubtreeTransitive(n1, n2R, n3)
        }
      }
    }
    else {
      lem_rightIsAlsoInRightSubtree(n1, n2)
    }
  } ensuring (_ => isInRightSubtree(n3, n1))

  def lem_isInRightSubtreeTransitive(n1: SkipNode, n2: SkipNode, n3: Int): Unit = {
    require(isInRightSubtree(n2, n1))
    require(isInRightSubtree(n3, n2))
    if (n1.right != n2) {
      assert(isInRightSubtree(n2, n1.right))
      assert(n1.right.isSkipNode)
      n1.right match {
        case r@SkipNode(_, _, _, _) => lem_isInRightSubtreeTransitive(r, n2, n3)
      }
    }
  } ensuring (isInRightSubtree(n3, n1))

  // Proof that isInRightSubtree(node, node) implies isInRightSubtree(v, node)
  def lem_isInRightSubtreeImpliesValueIsAlsoIn(n: Node, target: Node, v: Int): Unit = {
    require(n.isSkipNode)
    require(target.hasValue(v))
    require(isInRightSubtree(target, n))
    decreases(sizeRight(n))
    n match {
      case n@SkipNode(_, _, right, _) => {
        if (target != right) {
          right match {
            case r@SkipNode(_, _, _, _) => {
              lem_isInRightSubtreeImpliesValueIsAlsoIn(r, target, v)
            }
          }
        }
      }
    }
  } ensuring (_ => isInRightSubtree(v, n))

  def lem_isInRightSubtreeImpliesSelfValueIsLower(n: SkipNode, k: Int): Unit = {
    require(n.isSkipList)
    require(isInRightSubtree(k, n))
    decreases(sizeRight(n))
    n.right match {
      case right@SkipNode(value, _, _, _) => if (value != k) {
        lem_isInRightSubtreeImpliesSelfValueIsLower(right, k)
      }
    }
  } ensuring (_ => n.value < k)

  def lem_inRightSubtreeImpliesDifference(n: Node, x: Node): Boolean = {
    require(isInRightSubtree(x, n))
    lem_inRightSubtreeImpliesLowerMeasure(n, x)
    n != x
  }.holds

  def lem_isInRightSubtreeInequality(n: Node, a: Node, v: Int): Unit = { 
    require(n.isSkipList)
    require(isInRightSubtree(a, n))
    require(isInRightSubtree(v, n))
    require(a.valueSmallerThan(v))
    n match {
      case SkipNode(_, _, right, _) => {
        if (right != a) {
          right match {
            case SkipNode(value, _, _, _) => {
              lem_rightSubtreeDoesNotSkipValues(n, a, v)
              lem_isInRightSubtreeInequality(right, a, v)
            }
          }
        }
      }
    }
  } ensuring (_ => isInRightSubtree(v, a))

  def lem_inRightSubtreeHasSameHeight(n: SkipNode, x: SkipNode): Unit = {
    require(n.isSkipList)
    require(x.isSkipList)
    require(isInRightSubtree(x, n))
    n.right match {
      case r@SkipNode(_, _, _, _) => {
        if (x != r) {
          lem_inRightSubtreeHasSameHeight(r, x)
        }
      }
    }
  } ensuring (n.height == x.height)

  def lem_inRightSubtreeHasSameNodeHeight(n: Node, x: Node): Unit = {
    require(n.isSkipList)
    require(x.isSkipList)
    require(n.isSkipNode)
    require(x.isSkipNode)
    require(isInRightSubtree(x, n))
    (n, x) match {
      case (n@SkipNode(_, _, _, hN), x@SkipNode(_, _, _, hX)) => {
        lem_inRightSubtreeHasSameHeight(n, x)
      }
    }
  } ensuring (nodeHeight(n) == nodeHeight(x))

  def lem_rightSubtreeDoesNotSkipValues(n: Node, a: Node, v: Int): Unit = {
    require(n.isSkipList)
    require(isInRightSubtree(a, n))
    require(isInRightSubtree(v, n))
    require(a.valueSmallerThan(v))
    require(rightNodeIsNot(n, a))
    n match {
      case n@SkipNode(_, _, right, _) => (right, a) match {
        case (right@SkipNode(value, _, _, _), a@SkipNode(valueA, _, _, _)) => {
          lem_isInRightSubtreeImpliesValueIsAlsoIn(right, a, valueA)
          lem_isInRightSubtreeImpliesSelfValueIsLower(right, valueA)
        }
      }
    }
  } ensuring (_ => rightNodeHasValueLessThan(n, v))

//_____________________________________________ NEWDOWN proof

def lem_newDownReturnsSkipList(t: Node, v: Int): Unit = {
  require(t.isSkipList)
  t match {
    case t@SkipNode(value, _, right, _) => {
      if (value != v) {
        lem_newDownReturnsSkipList(right, v)
      }
    }
    case Leaf => ()
  }
} ensuring (_ => findNewDown(t, v).isSkipList)

// Proof that if newDown contains k, it returns a skipnode of value k
def lem_newDownReturnsSkipNodeOfValue(n: Node, v: Int): Unit = {
    require(n.isSkipList)
    require(isInRightSubtree(v, n))
    decreases(size(n))
    n match {
      case n@SkipNode(value, _, r, h) => {
        r match {
          case SkipNode(valueR, _, _, _) => {
            if (v != valueR) {
              assert(isInRightSubtree(v, r))
              r match {
                case r@SkipNode(_,_,_,_) => {
                  lem_isInRightSubtreeTransitive(n, r, v)
                  lem_sizeSkipNodeIsPositive(r)
                }
              }
              sizeDecreasesToTheRight(n)
              lem_newDownReturnsSkipNodeOfValue(r, v)
            }
          }
        }                         
      }
    }   
  }.ensuring(_=> findNewDown(n, v).hasValue(v) && hasSameHeight(findNewDown(n, v), n))

  def lem_newDownWithTooHighKeyNodeReturnsLeaf(n: Node, k: Int): Unit = {
    require(n.isSkipList)
    require(n.valueHigherThan(k))
    decreases(sizeRight(n))
    n match {
      case SkipNode(_, _, right, _) => right match {
        case right@SkipNode(_, _, _, _) => {
          lem_newDownWithTooHighKeyNodeReturnsLeaf(right, k)
        }
        case Leaf => ()
      }
    }
  } ensuring (_ => findNewDown(n, k) == Leaf)

//_____________________________________________ level leftmost proof

// Leftmost element from currentLevel
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
//_____________________________________________ HEIGHT proofs and lemmas
  // All nodes in skipList have their height upper bounded
  def hasMaxHeight(sl: SkipList): Boolean = { 
    require(sl.isSkipList)
    hasMaxHeight(sl.maxHeight, sl.head)
  }.holds

  def hasMaxHeight(maxHeight: BigInt, t: Node): Boolean = {
    require(t.isSkipList)
    require(t.isLeaf || t.heightAtMost(maxHeight))
    t match {
      case SkipNode(_, down, right, height) => (
        height <= maxHeight && 
        hasMaxHeight(maxHeight, down) &&
        hasMaxHeight(maxHeight, right)
      )
      case Leaf => true
    }
  }.holds

//___________________________________________________________________________________________________________________________
//__________________________________________________________ TESTING ______________________________________________________
//___________________________________________________________________________________________________________________________



  // @ignore
  // def printList(sl: SkipList): Unit = {
  //   def printLevel(t: Node): Unit = t match {
  //     case Leaf => println("+inf]")
  //     case SkipNode(value, down, right, height) => {
  //       if (value ==BigInt.MinValue) {
  //         print("[" + value + ", ")
  //       }
  //       else {
  //         print(value + ", ")
  //       }
  //       printLevel(right)
  //     }
  //   }
  //   def printList_(t: Node): Unit = t match {
  //     case Leaf => println()
  //     case SkipNode(value, down, right, height) => {printLevel(t); printList_(down)}
  //   }
  //   printList_(sl.head)
  // }

  
  // @ignore
  // def randomAction(rd: Random, sl: SkipList, upperBoundElems:BigInt): SkipList = {
  //   val elem = rd.nextInt(upperBoundElems)
  //   rd.nextInt(3) match {
  //     case 0 => {
  //       println("Searching for " + elem)
  //       if (isIn(sl, elem)) {
  //         println("Found")
  //       }
  //       else {
  //         println("Not found")
  //       }
  //       println()
  //       sl
  //     }
  //     case 1 => {
  //       println("Inserting " + elem)
  //       val resultList = insert(sl, elem)
  //       printList(resultList)
  //       resultList
  //     }
  //     case 2 => {
  //       println("Removing " + elem)
  //       val resultList = remove(sl, elem)
  //       printList(resultList)
  //       resultList
  //     }
  //   }
  // }

  // @ignore
  // def initSL(): SkipList = {
  //   val firstNode = SkipNode(Int.MinValue, Leaf, Leaf, 0)
  //   return SkipList(firstNode, 0)
  // }
  // @ignore
  // def main(args: Array[String]): Unit = {
  //   val nOps = 50
  //   val upperBoundElems = 100
  //   val r = new Random
  //   val sl = initSL()
  //   (0 until nOps).foldLeft(sl)((tmpList, _) => randomAction(r, tmpList, upperBoundElems))
  // }
}