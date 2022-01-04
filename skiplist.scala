package users
import users.utils._
import users.axioms._
import users.proofs._
import users.properties._

import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

package object skiplist {

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
    def getValue(): Int = this match {case SkipNode(v, _, _, _) => v; case _ => Int.MaxValue} 
  }

  case class SkipList(head: Node, maxHeight: BigInt) {
    def isSkipList = isASkipList(this)
  }

  case class SkipNode(value: Int, down: Node, right: Node, height: BigInt) extends Node
  case object Leaf extends Node

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
  
  def insertUpwards(k: Int, desiredHeight: BigInt, topLeftmost: Node, currentLeftmost: Node, currentLevel: BigInt, lowerLeftmost: Node): Node = {
    // insertRight in levels 0 to maxHeight
    // if desiredHeight is lower than level, simply updates links to the new subtree
    require(topLeftmost.isSkipList)
    require(lowerLeftmost.isSkipList)
    require(currentLeftmost.isSkipList)
    require(topLeftmost.isSkipNode)
    require(currentLeftmost.isSkipNode)
    require(topLeftmost.hasValue(Int.MinValue))
    require(lowerLeftmost.hasValue(Int.MinValue))
    require(desiredHeight >= 0)
    require(currentLevel <= nodeHeight(topLeftmost))
    require(desiredHeight <= nodeHeight(topLeftmost))
    require(currentLevel >= 1)
    require((currentLevel >= (desiredHeight + 1)) || isInRightSubtree(k, lowerLeftmost))
    require(k > Int.MinValue)
    require(nodeHeight(currentLeftmost) == currentLevel)
    require(isLowerOf(currentLeftmost, topLeftmost))
    require(currentLevel == 0 || 
      (lowerLeftmost.isSkipNode && isSubsetOf(currentLeftmost, lowerLeftmost) && (nodeHeight(lowerLeftmost) + 1 == currentLevel)))
    decreases(nodeHeight(topLeftmost) + 1 - currentLevel)

    lem_isLowerOfImpliesSameValue(currentLeftmost, topLeftmost)
    
    if (currentLevel == nodeHeight(topLeftmost)) { // Last insert, don't recurse upwards
      //plug lower level
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      lem_plugLowerLevelReturnsSkipList(currentLeftmost, lowerLeftmost)
      lem_plugLowerLevelOnSameValueIsLowerOf(currentLeftmost, lowerLeftmost)
      //insert right
      if (currentLevel > desiredHeight) {
        updatedCurrentLeftmost
      }
      else {
        val finalCurrentLeftmost = updatedCurrentLeftmost match {
          case updatedCurrentLeftmost@SkipNode(_, _, _, _) => {
            lem_insertRightReturnsSkipList(updatedCurrentLeftmost, k)
            insertRight(updatedCurrentLeftmost, k)
          }
        }
        finalCurrentLeftmost
      }
    }
    
    else if (currentLevel <= desiredHeight) { // Insert at current level and recurse upwards
      //plug lower level
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      assert(currentLeftmost.hasValue(Int.MinValue))
      assert(lowerLeftmost.hasValue(Int.MinValue))
      lem_plugLowerLevelOnSameValueIsLowerOf(currentLeftmost, lowerLeftmost)

      //insert right
      val finalCurrentLeftmost = updatedCurrentLeftmost match {
        case updatedCurrentLeftmost@SkipNode(_, _, _, _) => {
          lem_plugLowerLevelReturnsSkipList(currentLeftmost, lowerLeftmost)
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
      lem_insertRightReturnsSkipList(updatedCurrentLeftmost, k)
      lem_isSubsetOfTransitivity(nextCurrentLeftmost, updatedCurrentLeftmost, finalCurrentLeftmost)
      lem_insertRightContainsKey(updatedCurrentLeftmost, k)
      lem_insertRightReturnsSkipList(updatedCurrentLeftmost, k)
      val x = insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, finalCurrentLeftmost)
      lem_isLowerOfTransitivity(x, finalCurrentLeftmost, lowerLeftmost)
      x
    }
    else { // plug and recurse upwards
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      assert(currentLeftmost.hasValue(Int.MinValue))
      assert(lowerLeftmost.hasValue(Int.MinValue))
      lem_plugLowerLevelOnSameValueIsLowerOf(currentLeftmost, lowerLeftmost)
      val nextCurrentLeftmost = levelLeftmost(topLeftmost, currentLevel+1)
      lem_plugLowerLevelReturnsSkipList(currentLeftmost, lowerLeftmost)
      lem_isDownOf(topLeftmost, nextCurrentLeftmost, currentLeftmost, currentLevel)
      lem_isDownOfImpliesSubset(currentLeftmost, nextCurrentLeftmost)
      lem_plugLowerLevelReturnsSuperset(currentLeftmost, lowerLeftmost)
      lem_isSubsetOfTransitivity(nextCurrentLeftmost, currentLeftmost, updatedCurrentLeftmost)
      val x = insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, updatedCurrentLeftmost)
      lem_isLowerOfTransitivity(x, updatedCurrentLeftmost, lowerLeftmost)
      x
    }
  } ensuring(res => res.isSkipList && 
                    res.hasValue(Int.MinValue) && 
                    isLowerOf(lowerLeftmost, res) && 
                    nodeHeight(res) == nodeHeight(topLeftmost))

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
    require(n.valueAtMost(k))
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

  def insert(sl: SkipList, k: Int, height: BigInt): SkipList = {
    require(sl.isSkipList)
    require(height >= 0)
    
    // if needed, bring first value to same height
    val newHead = if (height > nodeHeight(sl.head)) {
                    assert(height > nodeHeight(sl.head))
                    lem_increaseHeightReturnsSkiplist(sl.head, height)
                    lem_increaseHeightReturnsMinValueNode(sl.head, height)
                    lem_increaseHeightReturnsHigherNode(sl.head, height)
                    increaseHeight(sl.head, height)
                  } else {
                    check(height <= nodeHeight(sl.head))
                    sl.head
                  }

    assert(newHead.isSkipList)
    assert(newHead.hasValue(Int.MinValue))
    assert(height <= nodeHeight(newHead))

    if(k == Int.MinValue) {
      assert(headIsMinInt(sl))
      assert(isInTheList(k, sl))
      return sl
    }

    val zeroLeftmost = levelLeftmost(newHead, 0)
    assert(zeroLeftmost.isSkipNode)
    val levelZero = zeroLeftmost match {
      case z@SkipNode(_,_,_,_) => 
        lem_insertRightZeroHeightIsSkipList(z,k)
        lem_insertRightZeroHeightContainsK(z,k)
        lem_insertRightZeroHeightReturnsSuperset(z,k)
        insertRightZeroHeight(z, k)
    } 
    assert(isInRightSubtree(k, levelZero))
    assert(isInTheList(k, levelZero))

    if(nodeHeight(newHead) > 0) {
      val oneLeftmost = levelLeftmost(newHead, 1)
      assert(oneLeftmost.isSkipList)
      assert(oneLeftmost.hasValue(Int.MinValue))
      assert(nodeHeight(oneLeftmost) == 1)
      lem_isDownOf(newHead, oneLeftmost, zeroLeftmost, 0)
      lem_isDownOfImpliesSubset(zeroLeftmost, oneLeftmost)
      lem_isSubsetOfTransitivity(oneLeftmost, zeroLeftmost, levelZero)
      assert(isLowerOf(oneLeftmost,newHead))
      assert(k > Int.MinValue)
      val newNewHead = insertUpwards(k, height, newHead, oneLeftmost, 1, levelZero)
      assert(newNewHead.isSkipList)
      assert(newNewHead.hasValue(Int.MinValue))
      assert(isLowerOf(levelZero, newNewHead))
      lem_isInListIfInZero(k, newNewHead, levelZero)
      if(sl.maxHeight < height) {
        val x = SkipList(newNewHead, height)
        assert(x.head.hasValue(Int.MinValue))
        assert(nodeHeight(newNewHead) == height)
        assert(headIsMinInt(x))
        assert(x.isSkipList)
        x
      }
      else {
        val x = SkipList(newNewHead, sl.maxHeight)
        assert(x.head.hasValue(Int.MinValue))
        assert(nodeHeight(x.head) == x.maxHeight)
        assert(headIsMinInt(x))
        assert(x.isSkipList)
        x
      }
      
    }
    else {
      assert(isInTheList(k, levelZero))
      SkipList(levelZero,  max(sl.maxHeight, height))
    }
  } ensuring ( res => isInTheList(k, res) && res.isSkipList)
}