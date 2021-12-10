import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._

object SkipList {
  sealed abstract class Node
  case class SkipList(head: Node, maxHeight: BigInt)
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

  // def insert(t: Node, k: Int, insertHeight: Int): Node = {
  //   require(isSkipList(t))
  //   require(insertHeight >= 0)
  //   require(size(t) >= 0)
  //   decreases(size(t))
  //   t match { // Returns the list with k inserted
  //     case sn@SkipNode(value, down, right, height) => {
  //       if (height > insertHeight) { // We are too high, recurse on lower level
  //         sizeIsNonNegative(down)
  //         sizeDecreasesDown(sn)
  //         elementOfSkipListIsSkipList(sn)
  //         SkipNode(value, insert(down, k, insertHeight), right, height)
  //       }
  //       else { //at correct level, insert lower, then insert right
  //         sizeIsNonNegative(down)
  //         sizeDecreasesDown(sn)
  //         val lowerLeftmostNode = insert(down, k, insertHeight)
  //         assert(isRight(lowerLeftmostNode, k))
  //         assert(isSkipList(lowerLeftmostNode))

  //         insertRight(t, k, lowerLeftmostNode) //insert right need new underlying level to update links to down nodes
  //       }
  //     }
  //     case Leaf => Leaf // Found a leaf (we are at level -1)
  //   }
  // }
  
  // Leftmost element from currentLevel
  def levelLeftmost(t: Node, level: BigInt): Node = {
    require(isSkipList(t))
    require(isSkipNode(t))
    require(level >= 0)
    // TODO require(nodeHeight(t) >= level)
    t match {
      case sn@SkipNode(_,down,_,height) =>
        if (height > level) {levelLeftmost(down, level)}
        else {sn}
      case Leaf => Leaf // Will not happen because of require
    }
  }

  // def insertUpwards(k: Int, desiredHeight: BigInt, topLeftmost: Node, currentLevel: BigInt, lowerLeftmost: Node): Node = {
  //   // insertRight in levels 0 to maxHeight
  //   // if desiredHeight is lower than level, simply updates links to the new subtree
  //   require(isSkipList(topLeftmost))
  //   require(isSkipList(lowerLeftmost))
  //   require(desiredHeight >= 0)
  //   require(currentLevel >= 0)
  //   // TODO decreases(nodeHeight(topLeft) - level)
  //   topLeftmost match {
  //     case topLeftmost@SkipNode(_,_,_,_) => {
  //       val currentLeftmost = levelLeftmost(topLeftmost, currentLevel)
  //       val newLevelLeftmost = insertRight(currentLeftmost, k, desiredHeight, lowerLeftmost)
  //       assert(isInRightSubtree(k, newLevelLeftmost))
  //       if (currentLevel < topLeftmost.height) {insertUpwards(k, desiredHeight, topLeftmost, currentLevel+1, newLevelLeftmost)}
  //       else newLevelLeftmost
  //     }
  //     case Leaf => Leaf //NOTE this should not happen
  //   }
  // }// .ensuring(_ => if(level < desiredHeight) isIn(newLevelLeft, k)) TODO

  // Note : lowerLeftmost is the new node under t with inserted value k
  // we need to update all links
  def insertRight(n: SkipNode, k: Int): Node = {
    require(isSkipList(n))
    require(size(n) >= 0)
    require(n.value <= k)
    require(isInRightSubtree(k, n.down)) // TODO : Also arrange case where height is 0 and there is nothing below
    decreases(size(n))
    if (n.value == k) {n}
    else {
      n.right match {
        case r@SkipNode(valueR, downR, rightR, heightR) => {
          if (valueR <= k) {
            sizeIsNonNegative(r)
            sizeDecreasesToTheRight(n)
            higherLevelIsSubsetofLowerOne(n, r)
            skipnodeToTheRightAlsoHasKeyToTheRight(n.down, r.down, k)
            val newRight = insertRight(r, k)
            SkipNode(n.value, n.down, newRight, n.height)
          }
          else {
            val newDown = findNewDown(n.down, k)
            val newRight = SkipNode(k, newDown, n.right, n.height)
            SkipNode(n.value, n.down, newRight, n.height)
          }
        }
        case Leaf => {
          val newDown = findNewDown(n.down, k)
          val newRight = SkipNode(k, newDown, Leaf, n.height)
          SkipNode(n.value, n.down, newRight, n.height)
        }
      }
    }
  }

  def skipnodeToTheRightAlsoHasKeyToTheRight(n: Node, r: Node, k: Int): Unit = {
    require(isSkipNode(n))
    require(isSkipNodeOfValueAtMost(r, k))
    require(isSkipList(n))
    require(isSkipList(r))
    require(isInRightSubtree(r, n))
    require(isInRightSubtree(k, n))
  } ensuring (_ => isInRightSubtree(k, r))

  def plugLowerLevel(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Node = {
    oldCurrentLeftmost match {
      case SkipNode(value, down, right, height) => {
        val newDown = findNewDown(newLowerLeftmost, value)
        SkipNode(value, newDown, plugLowerLevel(right, newDown), height)
      }
      case Leaf => Leaf
    }
  }

  def plugLowerLevelReturnsSkipList(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Unit = {
    require(isSkipList(oldCurrentLeftmost))
    require(isSkipList(newLowerLeftmost))
    // TODO : require(old has height height(new) + 1)
    // TODO : require(newLowerLeftmost is superset of oldCurrentLeftmost)
  } ensuring (isSkipList(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)))

  // boil node up to level newHeight
  def increaseHeight(n: Node, newHeight:BigInt): Node = {
    require(isSkipList(n))
    require(newHeight >= nodeHeight(n))
    decreases(newHeight - nodeHeight(n))
    n match {
      case n@SkipNode(value, down, right, height) => {
        if (height >= newHeight) {
          n
        } 
        else {
          nodeHeightIsNonNegative(n)
          nodeHeightisNodeHeight(n)
          increaseHeight(SkipNode(value, n, Leaf, height+1), newHeight)
        }
      }
      case Leaf => Leaf
    }
  }

  def nodeHeightisNodeHeight(n: SkipNode): Unit = {
    require(isSkipList(n))
    require(nodeHeight(n) >= 0)
    decreases(nodeHeight(n))
    n.down match {
      case SkipNode(_, down, _, _) => {
        down match {
          case down@SkipNode(_, _, _, _) => {nodeHeightIsNonNegative(down); nodeHeightisNodeHeight(down)}
          case Leaf => ()
        }
        
      }
      case Leaf => ()
    }
  } ensuring (_ => nodeHeight(n) == n.height)

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

  def findNewDown(t: Node, v: Int): Node = t match {
    case SkipNode(value, down, right, height) => 
      if (value == v) {t} 
      else {findNewDown(right, v)}
    case Leaf => Leaf
  }

  // def remove(sl: SkipList, k:BigInt): SkipList = {
  //   require(isSkipList(sl))
  //   require(k !=BigInt.MinValue)
  //   sizeIsNonNegative(sl.head)
  //   SkipList(remove(sl.head, k), sl.maxHeight)
  // }

  // def remove(t: Node, k:BigInt): Node = {
  //   require(isSkipList(t))
  //   require(size(t) >= 0)
  //   decreases(size(t))
  //   t match { // Returns the list with k removed
  //     case t@SkipNode(value, down, right, height) => {
  //       sizeDecreasesDown(t)
  //       sizeIsNonNegative(down)
  //       val lowerLeftmostNode = remove(down, k)
  //       sizeIsNonNegative(t)
  //       //removeReturnsSkipList(down, k)
  //       // assert(isSkipList(lowerLeftmostNode)) // TODO : prove remove returns valid skiplist node
  //       removeRight(t, k, lowerLeftmostNode)
  //     }
  //     case Leaf => Leaf // Found a leaf (we are at level -1)
  //   }
  // }
  
  // def removeRight(t: Node, k:BigInt, lowerLevel: Node): Node = {
  //   require(isSkipList(t))
  //   require(isSkipList(lowerLevel))
  //   require(size(t) >= 0)
  //   decreases(size(t))
  //   sizeIsNonNegative(t)
  //   t match {
  //     case t@SkipNode(value, down, right, height) => {
  //       val newDown = findNewDown(lowerLevel, value)
  //       newDownReturnsSkipList(lowerLevel, value)
  //       right match {
  //         case SkipNode(valueR, downR, rightR, heightR) => {
  //           if (valueR == k) { // Remove right
  //             assert(isInRightSubtree(rightR, t))
  //             nodeHeightIsNonNegative(t)
  //             sizeAtRightIsLower(t, rightR)
  //             sizeIsNonNegative(rightR)
  //             SkipNode(value, newDown, removeRight(rightR, k, newDown), height)
  //           }
  //           else { // Value is not the next node, just recurse to the right
  //             sizeDecreasesToTheRight(t)
  //             sizeIsNonNegative(right)
  //             SkipNode(value, newDown, removeRight(right, k, newDown), height)
  //           }
  //         }
  //         case Leaf => SkipNode(value, newDown, Leaf, height) // Reached end of this level, just update lower node
  //       }
  //     }
  //     case Leaf => Leaf
  //   }
  // }

  def isIn(sl: SkipList, k: Int): Boolean = {
    search(sl, k) match {
      case None() => false
      case Some(value) => true
    }
  }
  

//__________________________________________________________AXIOMS______________________________________________________

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

  // Return true when a node target is in the subtree of a node of
  // TODO: Leaf,_ not necessarly ??
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

  def levelsAxiom(t: Node): Boolean = {
    t match {
      case SkipNode(value, down, right, height) => right match {
        case SkipNode(_, downR, _, _) => levelsAxiom(down) && levelsAxiom(right) && isInRightSubtree(downR, down)
        case Leaf => levelsAxiom(down)
      }
      case Leaf => true
    }
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

  // Return true when the given Skiplist is indeed a skiplist given the previous axioms
  def isSkipList(sl: SkipList): Boolean = {
    if (!headIsMinInt(sl)) {false}
    else if (hasNonNegativeHeight(sl.head)) {
      heightDecreasesDown(sl.head) && increasesToTheRight(sl.head) && levelsAxiom(sl.head)
    }
    else {false}
  }

  // Return true when the given node represent a skiplist (exept for the head condition)
  def isSkipList(t: Node): Boolean = {
    if (hasNonNegativeHeight(t)) {
      heightDecreasesDown(t) && increasesToTheRight(t) && levelsAxiom(t)
    }
    else {false}
  }

  // The node height, all the leaf are at height 0, skipnode at height l+1 where l is their height attribute
  def nodeHeight(n: Node): BigInt = n match {
    case SkipNode(_,d,_,h) => if (h == 0) {0} else {nodeHeight(d)+1}
    case Leaf => 0
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
    require(isSkipList(n))
    require(isSkipList(x))
    require(isInRightSubtree(x, n))
    if (n.right != x) {
      n.right match {
        case r@SkipNode(_, _, _, _) => {
          higherLevelIsSubsetofLowerOne(r, x)
          (n.down, r.down, x.down) match {
            case (nD@SkipNode(_, _, _, _), rD@SkipNode(_, _, _, _), xD@SkipNode(_, _, _, _)) => isInRightSubtreeTransitive(nD, rD, xD)
            case _ => ()
          }
        }
      }
    }
  } ensuring (_ => isInRightSubtree(x.down, n.down))

  def higherLevelIsSubsetofLowerOne(v: Int, n: SkipNode): Unit = {
    require(isSkipList(n))
    require(isInRightSubtree(v, n))
    assert(isSkipNode(n.right))
    n.right match {
      case r@SkipNode(valueR, downR, _, _) => {
        if (v != valueR) {
          higherLevelIsSubsetofLowerOne(v, r)
          (r.down, n.down) match {
            case (rD@SkipNode(_, _, _, _), nD@SkipNode(_, _, _, _)) => isInRightSubtreeTransitive(nD, rD, v)
          }
        }
        else {
          (r.down, n.down) match {
            case (rD@SkipNode(_, _, _, _), nD@SkipNode(_, _, _, _)) => isInRightSubtreeImpliesValueIsAlsoIn(nD, rD)
          }
        }
      }
    }
  } ensuring (_ => isInRightSubtree(v, n.down))

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

  def searchFindsElement(n: Node, v:BigInt): Unit = {
    require(isSkipList(n))
    require(isInTheList(v,n))  
    n match {
      case Leaf => ()
      case SkipNode(value, down, right, height) => {
        if(isInRightSubtree(v, right)){
          (assume(isInRightSubtree(v, right)))
        } else {
          assume(isInTheList(v,down))

        }
      }
    }
  } ensuring (_ => search(n,v) == Some(v)
  
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
  //_________________________________________________________LEMMAS____________________________________________________
  
  // Lemmas for 8
  

  
  def elementOfSkipListIsSkipList(t: SkipNode): Unit = { // Is not used in proofs, but keep it there to make sure we don't break SkipList axioms
  require(isSkipList(t))
  assert(levelsAxiom(t.down))
  assert(levelsAxiom(t.right))
  } ensuring (_ => isSkipList(t.down) && isSkipList(t.right))


  // Proof of maxHeightIsMaxHeight for both nodes and skiplists
  def hasUpperBoundedHeight(maxHeight:BigInt, t: Node) = t match {
    case SkipNode(_, _, _, height) => height <= maxHeight
    case Leaf => true
  }

  def downAndRightHaveUpperBoundedHeight(maxHeight:BigInt, t: Node) = t match {
    case SkipNode(_, d, r, height) => height <= maxHeight && hasUpperBoundedHeight(maxHeight, d) && hasUpperBoundedHeight(maxHeight, r)
    case Leaf => true 
  }

  def heightIsLessThanMaxHeight(maxHeight:BigInt, t: Node): Unit = {
    require(isSkipList(t))
    require(hasUpperBoundedHeight(maxHeight, t))
  } ensuring (_ => downAndRightHaveUpperBoundedHeight(maxHeight, t))

  def maxHeightIsMaxHeight(maxHeight:BigInt, t: Node): Boolean = t match {
    case SkipNode(_, down, right, height) => (
      height <= maxHeight && 
      maxHeightIsMaxHeight(maxHeight, down) &&
      maxHeightIsMaxHeight(maxHeight, right)
    )
    case Leaf => true
  }

  def maxHeightIsMaxHeightLemma(maxHeight:BigInt, t: SkipNode): Unit = {
    require(isSkipList(t))
    require(t.height <= maxHeight)
    t.right match {
      case r@SkipNode(_, _, _, _) => maxHeightIsMaxHeightLemma(maxHeight, r)
      case Leaf => ()
    }
    t.down match {
      case d@SkipNode(_, _, _, _) => maxHeightIsMaxHeightLemma(maxHeight, d)
      case Leaf => ()
    }
  } ensuring (_ => maxHeightIsMaxHeight(maxHeight, t))

  def maxHeightIsMaxHeightLemma(sl: SkipList): Unit = {
    require(isSkipList(sl))
    sl.head match {
      case h@SkipNode(value, down, right, height) => maxHeightIsMaxHeightLemma(sl.maxHeight, h)
      case Leaf => ()
    }
  } ensuring (_ => maxHeightIsMaxHeight(sl.maxHeight, sl.head))


  // Proof of isInRightSubTree transitivity : Lemmas that didn't even need to be proven :
  // If x is in n's right subtree and n.down is not a Leaf, then x.down is not a Leaf
  // If x is in n's right subtree then n is not a Leaf
  def rightIsAlsoInRightSubtree(n: SkipNode, x: SkipNode): Unit = {
    require(isInRightSubtree(x, n))
    n.right match {
      case Leaf => ()
      case r@SkipNode(value, down, right, height) => {
        if (r != x) {
          rightIsAlsoInRightSubtree(r, x)
        } 
      }
    }
  } ensuring (_ => isInRightSubtree(x.right, n))

  def isInRightSubtreeTransitive(n1: SkipNode, n2: SkipNode, n3: SkipNode): Unit = {
    require(isInRightSubtree(n2, n1))
    require(isInRightSubtree(n3, n2))
    if (n3 != n2.right) {
      rightIsAlsoInRightSubtree(n1, n2)
      n2.right match {
        case n2R@SkipNode(_, _, _, _) => {
          isInRightSubtreeTransitive(n1, n2R, n3)
        }
      }
    }
    else {
      rightIsAlsoInRightSubtree(n1, n2)
    }
  } ensuring (_ => isInRightSubtree(n3, n1))

  def isInRightSubtreeTransitive(n1: SkipNode, n2: SkipNode, n3: Int): Unit = {
    require(isInRightSubtree(n2, n1))
    require(isInRightSubtree(n3, n2))
    if (n1.right != n2) {
      assert(isInRightSubtree(n2, n1.right))
      assert(isSkipNode(n1.right))
      n1.right match {
        case r@SkipNode(_, _, _, _) => isInRightSubtreeTransitive(r, n2, n3)
      }
    }
  } ensuring (isInRightSubtree(n3, n1))

  // Proof that size(right) decreases
  def sizeRightIsNonNegative(t: Node): Unit = {
    t match {
      case Leaf => ()
      case SkipNode(value, down, right, height) => sizeRightIsNonNegative(right)
    }
  }.ensuring(_ => sizeRight(t) >= 0)

  def sizeIsNonNegative(t: Node): Unit = {
    t match {
      case Leaf => ()
      case SkipNode(value, down, right, height) => {
        sizeIsNonNegative(down)
        sizeRightIsNonNegative(right)
      }
    }
  }.ensuring(_ => size(t) >= 0)
  
  def nodeHeightIsNonNegative(t: Node): Unit = {
    t match {
      case Leaf => ()
      case SkipNode(value, down, right, height) => nodeHeightIsNonNegative(down)
    }
  }.ensuring(_ => nodeHeight(t) >= 0)

  def sizeSkipNodeIsPositive(t: SkipNode): Unit = {
    sizeIsNonNegative(t.down)
    sizeRightIsNonNegative(t.right)
  } ensuring (_ => size(t) > 0)

  def isLeafOrSizeAtRightIsLower(n: Node, x: Node): Boolean = (n, x) match {
    case (Leaf, _) => true
    case (_, Leaf) => true
    case (n@SkipNode(_, _, _, _), x@SkipNode(_, _, _, _)) => size(n) > size(x)
  }

  def inRightSubtreeImpliesDifference(n: Node, x: Node): Unit = {
    require(isInRightSubtree(x, n))
    sizeRightIsNonNegative(n)
    inRightSubtreeImpliesLowerMeasure(n, x)
  } ensuring (_ => n != x)
  
  def inRightSubtreeImpliesLowerMeasure(n: Node, x: Node): Unit = {
    require(isInRightSubtree(x, n))
    require(sizeRight(n) >= 0)
    decreases(sizeRight(n))
    sizeRightIsNonNegative(n)
    n match {
      case n@SkipNode(value, down, right, height) => {
        if (x != right) {
          x match {
            case x@SkipNode(_, _, _, _) => {
              inRightSubtreeImpliesLowerMeasure(right, x)
            }
            case Leaf => ()
          }
        }
      }
    }
  } ensuring (_ => sizeRight(n) > sizeRight(x))

  def sizeAtRightIsLower(n: Node, x: Node): Unit = {
    require(isSkipList(n))
    require(isSkipList(x))
    require(isInRightSubtree(x, n))
    require(nodeHeight(n) >= 0)
    decreases(nodeHeight(n))
    n match {
      case n@SkipNode(_, down, right, _) => x match {
        case x@SkipNode(_, downR, rightR, _) => {
          sizeRightIsNonNegative(n)
          inRightSubtreeImpliesLowerMeasure(n, x)
          higherLevelIsSubsetofLowerOne(n, x)
          nodeHeightIsNonNegative(down)
          sizeAtRightIsLower(down, downR)
          down match {
            case (down@SkipNode(_, _, _, _)) => sizeSkipNodeIsPositive(down)
          }
        }
        case Leaf => ()
      }
      case Leaf => ()
    }
  } ensuring (_ => isLeafOrSizeAtRightIsLower(n, x))

  def sizeDecreasesToTheRight(n: SkipNode): Unit = {
    require(isSkipList(n))
    nodeHeightIsNonNegative(n)
    sizeAtRightIsLower(n, n.right)
    n.right match {
      case SkipNode(_, _, _, _) => assert(size(n) > size(n.right))
      case Leaf => {
        sizeSkipNodeIsPositive(n)
      }
    }
  } ensuring (_ => size(n) > size(n.right))

  def sizeDecreasesDown(n: SkipNode): Unit = {
    sizeRightIsNonNegative(n.right)
  } ensuring (_ => size(n) > size(n.down))


  // Proof that if newDown contains k, it returns a skipnode of value k
  def newDownReturnsNode(n: Node, v: Int): Unit = {
    require(isSkipList(n))
    require(size(n) >= 0)
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
                  isInRightSubtreeTransitive(n, r, v)
                  sizeSkipNodeIsPositive(r)
                }
              }
              sizeDecreasesToTheRight(n)
              newDownReturnsNode(r, v)
            }
          }
        }
      }
    }
  }.ensuring(_=> isSkipNodeOfValue(findNewDown(n, v), v))

  // Proof that isInRightSubtree(node, node) implies isInRightSubtree(v, node)
  def isInRightSubtreeImpliesValueIsAlsoIn(n: SkipNode, target: SkipNode): Unit = {
    require(isSkipList(n))
    require(isSkipList(target))
    require(isInRightSubtree(target, n))
    if (target != n.right) {
      n.right match {
        case r@SkipNode(_, _, _, _) => isInRightSubtreeImpliesValueIsAlsoIn(r, target)
      }
    }
  } ensuring (_ => isInRightSubtree(target.value, n))


  @extern
  def assume(b: Boolean): Unit = {
    (??? : Unit)
  } ensuring (_ => b)


  // Auxiliary functions
  def isSkipNode(n: Node): Boolean = n match {case Leaf => false; case _ => true}
  def isSkipNodeOfValue(n: Node, k: Int): Boolean = n match {case SkipNode(k, _, _, _) => true; case _ => false}
  def isSkipNodeOfValueAtMost(n: Node, k: Int): Boolean = n match {case SkipNode(v, _, _, _) => v <= k; case _ => false}
  def isLeaf(n: Node): Boolean = !isSkipNode(n)

  def size(t: Node): BigInt = t match {
    case SkipNode(value, down, right, height) => 1 + size(down) + sizeRight(right)
    case Leaf => 0
  }

  def sizeRight(t: Node): BigInt = t match {
    case SkipNode(value, down, right, height) => 1 + sizeRight(right)
    case Leaf => 0
  }
  
  def isInTheList(target: Int, of : Node): Boolean = of match {
    case SkipNode(value, down, right, height) => isInRightSubtree(target,of) || isInTheList(target,down)
    case Leaf => false
  }

  // def isInTheListImpliesisInTheListDown(target :BigInt, of : SkipNode): Unit = {
  //  require(isSkipList(of))
  //  require(isInTheList(target,of))
  //  require(of.height>=1)
  //  if(isInRightSubtree(x, n))
  //  assert(isSkipNode(of.down))
  //  of.right match {
  //    case a@SkipNode(v,d,r,h) => {
  //      lowerLevelIsSupersetofHigherOne(a,of)
  //    }
  //    case Leaf => ()
  //  }
  // } ensuring (_ => (isInTheList(target,of.down)))

  //  def isNotInTheListImpliesNotInRightSubList(target :BigInt, of : SkipNode): Unit = {
  //    require(isSkipList(of))
  //    require(!isInTheList(target,of))
  //    assert(!isInRightSubtree(target,of))
  //    assert(!isInRightSubtree(target,of.right))
  //    isInTheList(target,of.right)
  //    assert(!isInTheList(target,of.down))
  //    of.right match {
  //      case Leaf => ()
  //      case SkipNode(value, down, right, height) => assert(!isInTheList(target,down))
  //    }

  //  } ensuring (_ => (!isInTheList(target,of.right)))

  def isInTheList(target: Int, of: SkipList): Boolean = {
    return isInRightSubtree(target,of.head)
  }
  // } ensuring (_ => isInRightSubtree(n3, n1))

  // Auxiliary lemmas used to validate SkipList methods
  def newDownReturnsSkipList(t: Node, v: Int): Unit = {
    require(isSkipList(t))
    t match {
      case t@SkipNode(value, _, right, _) => {
        if (value != v) {
          newDownReturnsSkipList(right, v)
        }
      }
      case Leaf => ()
    }
  } ensuring (_ => isSkipList(findNewDown(t, v)))

  /*
  def newDownHasSameHeight(t: Node, v:Int): Unit = {
    require(isSkipList(t))
    t match {
      case t@SkipNode(value, _, right, _) => {
        assert(nodeHeight(right) == nodeHeight(t))
        if (value != v) {
          newDownHasSameHeight(right, v)
        }
      }
      case Leaf => ()
    }
  }.ensuring(_ => nodeHeight(findNewDown(t, v)) == nodeHeight(t))

  def isRight(t: Node, v:BigInt): Boolean = t match {
    case SkipNode(value, down, right, height) => if (value == v) true else {isRight(right, v)}
    case Leaf => false
  }
  
  def newDownAndContainsReturnsValue(t:Node, v:Int): Unit = {
    require(isSkipList(t))
    require(isRight(t,v))
    val nD = findNewDown(t, v) 
    assert(isSkipNode(nD))
  }
  */

  //_________________________________________________________TESTING___________________________________________________


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