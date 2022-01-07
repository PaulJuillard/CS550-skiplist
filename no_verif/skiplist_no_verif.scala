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
  if (currentLevel == nodeHeight(topLeftmost)) { // Last insert, don't recurse upwards
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      if (currentLevel > desiredHeight) {
        updatedCurrentLeftmost
      }
      else {
        val finalCurrentLeftmost = updatedCurrentLeftmost match {
          case updatedCurrentLeftmost@SkipNode(_, _, _, _) => {
            insertRight(updatedCurrentLeftmost, k)
          }
        }
        finalCurrentLeftmost
      }
    }
    else if (currentLevel <= desiredHeight) { // Insert at current level and recurse upwards
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      val finalCurrentLeftmost = updatedCurrentLeftmost match {
        case updatedCurrentLeftmost@SkipNode(_, _, _, _) => {
          insertRight(updatedCurrentLeftmost, k)
        }
      }
      val nextCurrentLeftmost = levelLeftmost(topLeftmost, currentLevel+1)
      val x = insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, finalCurrentLeftmost)
      x
    }
    else { // plug and recurse upwards
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      val nextCurrentLeftmost = levelLeftmost(topLeftmost, currentLevel+1)
      val x = insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, updatedCurrentLeftmost)
      x
    }
  }

  def plugLowerLevel(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Node = {
    (oldCurrentLeftmost, newLowerLeftmost) match {
      case (oldCurrentLeftmost@SkipNode(value, down, right, height), newLowerLeftmost@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(newLowerLeftmost, value)
        right match {
          case right@SkipNode(valueR, _, _, _) => {
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
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v == k) {n}
        else {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR <= k) {
                if (valueR == k) {
                  n
                }
                else {
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
    if (n.value == k) {n}
    else {
      n.right match {
        case r@SkipNode(valueR, downR, rightR, heightR) => {
          if (valueR <= k) {
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

  // boil first node up (Int.MinValue) to level newHeight
  def increaseHeight(n: Node, newHeight:BigInt): Node = {
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
    val newHead = if (height > nodeHeight(sl.head)) {
                    increaseHeight(sl.head, height)
                  } else {
                    sl.head
                  }
    if (k == Int.MinValue) {
      return sl
    }

    val zeroLeftmost = levelLeftmost(newHead, 0)
    val levelZero = zeroLeftmost match {
      case z@SkipNode(_,_,_,_) => 
        insertRightZeroHeight(z, k)
    }
    if(nodeHeight(newHead) > 0) {
      val oneLeftmost = levelLeftmost(newHead, 1)
      val newNewHead = insertUpwards(k, height, newHead, oneLeftmost, 1, levelZero)
      if(sl.maxHeight < height) {
        val x = SkipList(newNewHead, height)
        x
      }
      else {
        val x = SkipList(newNewHead, sl.maxHeight)
        x
      }
      
    }
    else {
      SkipList(levelZero,  max(sl.maxHeight, height))
    }
  }
}