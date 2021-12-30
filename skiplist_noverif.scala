import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

object SkipList {

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

  //_____________________________________________ INSERT

  def insertUpwards(k: Int, desiredHeight: BigInt, topLeftmost: Node, currentLeftmost: Node, currentLevel: BigInt, lowerLeftmost: Node): Node = {
    // insertRight in levels 0 to maxHeight
    // if desiredHeight is lower than level, simply updates links to the new subtree
    if (nodeHeight(topLeftmost) == 0) { // Only one insert to do, at level 0
      val finalCurrentLeftmost = currentLeftmost match {
        case currentLeftmost@SkipNode(value, _, _, _) => {
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
            insertRight(updatedCurrentLeftmost, k)
          }
        }
        finalCurrentLeftmost
      }
    }
    else if (currentLevel == 0) { // Insert at level 0 and recurse upwards
      val finalCurrentLeftmost = currentLeftmost match {
        case currentLeftmost@SkipNode(value, _, _, _) => {
          insertRightZeroHeight(currentLeftmost, k)
        }
      }
      val nextCurrentLeftmost = levelLeftmost(topLeftmost, currentLevel+1)
      insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, finalCurrentLeftmost)
    }
    else if (currentLevel <= desiredHeight) { // Insert at current level and recurse upwards
      //plug lower level
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      //insert right
      val finalCurrentLeftmost = updatedCurrentLeftmost match {
        case updatedCurrentLeftmost@SkipNode(_, _, _, _) => {
          insertRight(updatedCurrentLeftmost, k)
        }
      }
      //insert up
      val nextCurrentLeftmost = levelLeftmost(topLeftmost, currentLevel+1)
      insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, finalCurrentLeftmost)
    }
    else { // plug and recurse upwards
      val updatedCurrentLeftmost = plugLowerLevel(currentLeftmost, lowerLeftmost)
      val nextCurrentLeftmost = levelLeftmost(topLeftmost, currentLevel+1)
      insertUpwards(k, desiredHeight, topLeftmost, nextCurrentLeftmost, currentLevel+1, updatedCurrentLeftmost)
    }
  }

  def rightIsSubsetOfOtherRight(n: Node, lower: Node): Boolean = {
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

  def rightIsSkipNode(n: Node): Boolean = {
    n match {
      case SkipNode(_, _, right, _) => {
        right.isSkipNode
      }
    }
  }

  def isDownOf(down: Node, n: Node): Boolean = {
    n match {
      case SkipNode(_, d, _, _) => d == down
    }
  }

  def isRightOf(right: Node, n: Node): Boolean = {
    n match {
      case SkipNode(_, _, r, _) => r == right
    }
  }

  def levelBelowContainsK(n: Node, k: Int): Boolean = {
    n match {
      case n@SkipNode(_, down, _, _) => isInRightSubtree(k, down)
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

  // boil node up to level newHeight
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
    // if needed, bring first value to same height
    val newHead = if (height > nodeHeight(sl.head)) {increaseHeight(sl.head, height)} else {sl.head}
    
    if(k == Int.MinValue) return sl
    
    val currentLeftmost = sl.head
    SkipList(insertUpwards(k, height, newHead, currentLeftmost, 0, Leaf), max(sl.maxHeight, height))
  }

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

  def isLowerOf(lower: Node, n: Node): Boolean = {
    n match {
      case n@SkipNode(_, down, _, _) => n == lower || isLowerOf(lower, down)
      case Leaf => lower.isLeaf
    }
  }
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