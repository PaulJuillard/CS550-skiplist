import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._

object SkipList {
  sealed abstract class Node
  case class SkipList(head: Node, maxHeight: Int)
  case class SkipNode(value: Int, down: Node, right: Node, height: Int) extends Node
  case object Leaf extends Node
  
  def search(t: Node, target: Int): Option[Int] = t match {
    case SkipNode(v,d,r,_) =>
        if (v == target) { 
          Some(v) 
        }
        else {
          r match {
            case SkipNode(vR,_,_,_) => 
              if (vR <= target) { // If value is somewhere to the right, go right
                search(r, target)
              }
              else { // If not, try down
                search(d, target)
              }
            case Leaf => search(d, target) // Reached the end of this level, go down
          }
        }
    case Leaf => None()

  }
  def search(sl: SkipList, target: Int): Option[Int] = {
    search(sl.head, target)
  }

  // def insert(sl: SkipList, k: Int, height: Int): SkipList = {
  //   require(height >= 0)
  //   // val newHeight = min(sl.maxHeight + 1, height) // Removed due to not being useful, and causing addition overflow

  //   def insert_(t: Node, k: Int, insertHeight: Int): Node = {
  //     decreases(size(t))
  //     t match { // Returns the list with k inserted
  //       case SkipNode(value, down, right, height) => {
  //         if (height > insertHeight) { // We are too high, recurse on lower level
  //           SkipNode(value, insert_(down, k, insertHeight), right, height)
  //         }
  //         else {
  //           val lowerLeftmostNode = insert_(down, k, insertHeight)
  //           insertRight(t, k, lowerLeftmostNode)
  //         }
  //       }
  //       case Leaf => Leaf // Found a leaf (we are at level -1)
  //     }
  //   }

  //   def insertRight(t: Node, k: Int, lowerLevel: Node): Node = {
  //     decreases(size(t))
  //     t match {
  //       case SkipNode(value, down, right, height) => {
  //         val newDown = findNewDown(lowerLevel, value)
  //         right match {
  //           case SkipNode(valueR, downR, rightR, heightR) => {
  //             if ((valueR <= k) || (value >= k)) { // Key must be inserted further to the right, or we have passed the insertion point, simply update down
  //               SkipNode(value, newDown, insertRight(right, k, newDown), height)
  //             }
  //             else { // Insert to the right
  //               val insertedNode = SkipNode(k, Leaf, right, height) 
  //               SkipNode(value, newDown, insertRight(insertedNode, k, newDown), height)
  //             }
  //           }
  //           case Leaf => { // Reached end of list, we insert to the right if the current value is less than k
  //             if (value < k) { // Insert to the right
  //               val insertedNode = SkipNode(k, Leaf, Leaf, height) 
  //               SkipNode(value, newDown, insertRight(insertedNode, k, newDown), height)
  //             }
  //             else { // Just update down
  //               SkipNode(value, newDown, Leaf, height)
  //             }
  //           }
  //         }
  //       }
  //       case Leaf => Leaf
  //     }
  //   }

  //   def increaseHeight(t: Node, newHeight: Int): Node = {
  //     decreases(newHeight - height)
  //     t match {
  //       case SkipNode(value, down, right, height) => 
  //         if (height >= newHeight) {
  //           t
  //         } 
  //         else {
  //           increaseHeight(SkipNode(value, t, Leaf, height+1), newHeight)
  //         }
  //       case Leaf => Leaf
  //     }
  //   }

  //   SkipList(insert_(increaseHeight(sl.head, height), k, height), max(sl.maxHeight, height)) 
  // }

  // def insert(sl: SkipList, k: Int): SkipList = {
  //   if (isIn(sl, k)) {
  //     sl
  //   }
  //   def getRandomLevel(rd: Random, acc: Int): Int = {if (rd.nextInt(2) == 0) {acc} else {getRandomLevel(rd, acc+1)}}
  //   val r = new Random
  //   val height = getRandomLevel(r, 0)
  //   //println("random height : " + height)
  //   insert(sl, k, height)
  // }

  def findNewDown(t: Node, v: Int): Node = t match {
    case SkipNode(value, down, right, height) => if (value == v) {t} else {findNewDown(right, v)}
    case Leaf => Leaf
  }

/*
  def remove(sl: SkipList, k: Int): SkipList = {
    require(isSkipList(sl))
    require(k != Int.MinValue)
    sizeIsNonNegative(sl.head)
    SkipList(remove(sl.head, k), sl.maxHeight)
  }

  def remove(t: Node, k: Int): Node = {
    require(isSkipList(t))
    require(size(t) >= 0)
    decreases(size(t))
    t match { // Returns the list with k removed
      case t@SkipNode(value, down, right, height) => {
        sizeDecreasesDown(t)
        sizeIsNonNegative(down)
        val lowerLeftmostNode = remove(down, k)
        sizeIsNonNegative(t)
        //removeReturnsSkipList(down, k)
        // assert(isSkipList(lowerLeftmostNode)) // TODO : prove remove returns valid skiplist node
        removeRight(t, k, lowerLeftmostNode)
      }
      case Leaf => Leaf // Found a leaf (we are at level -1)
    }
  }
  
  def removeRight(t: Node, k: Int, lowerLevel: Node): Node = {
    require(isSkipList(t))
    require(isSkipList(lowerLevel))
    require(size(t) >= 0)
    decreases(size(t))
    sizeIsNonNegative(t)
    t match {
      case t@SkipNode(value, down, right, height) => {
        val newDown = findNewDown(lowerLevel, value)
        newDownReturnsValidElement(lowerLevel, value)
        right match {
          case SkipNode(valueR, downR, rightR, heightR) => {
            if (valueR == k) { // Remove right
              assert(isInRightSubtree(rightR, t))
              nodeHeightIsNonNegative(t)
              sizeAtRightIsLower(t, rightR)
              sizeIsNonNegative(rightR)
              SkipNode(value, newDown, removeRight(rightR, k, newDown), height)
            }
            else { // Value is not the next node, just recurse to the right
              sizeDecreasesToTheRight(t)
              sizeIsNonNegative(right)
              SkipNode(value, newDown, removeRight(right, k, newDown), height)
            }
          }
          case Leaf => SkipNode(value, newDown, Leaf, height) // Reached end of this level, just update lower node
        }
      }
      case Leaf => Leaf
    }
  }
*/
  def isIn(sl: SkipList, k: Int): Boolean = {
    search(sl, k) match {
      case None() => false
      case Some(value) => true
    }
  }

//__________________________________________________________AXIOMS______________________________________________________
  /* SkipList structural properties. They all must also be true recursively for the down and right nodes except the last one
  - heights >= 0

  - if(n.h > 0) n.b.height = n.height - 1 and n.val == v.b.val
  - if(n.h == 0) n.b is leaf

  - if(n.r is skipnode) n.r.v > n.r and n.r.h == n.h
  
  - if t has a right skipnode, then r.d is in t.d's right subtree (level)

  - skiplist.head is skipnode and skiplist.head.value = -inf
  */

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
      case SkipNode(_,d,r,0) => d match {
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

  def levelsAxiom(t: Node): Boolean = {
    t match {
      case SkipNode(value, down, right, height) => right match {
        case SkipNode(_, downR, _, _) => levelsAxiom(down) && levelsAxiom(right) && isInRightSubtree(downR, down)
        case Leaf => levelsAxiom(down)
      }
      case Leaf => true
    }
  }

  // Return true when the head of the given skiplist has the Int.MinValue value and has a height smaller than the max height
  def headIsMinInt(sl: SkipList) = sl.head match {
    case Leaf => false
    case SkipNode(value, down, right, height) => (
      value == Int.MinValue && 
      sl.maxHeight >= 0 && 
      height <= sl.maxHeight // TODO: why not == ?
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

  def east(n : Node): BigInt = {
    n match {
      case SkipNode(_,_,r,_) => 1 + east(r)
      case Leaf => 0
    }
  }

  def lem_right_east_less(n : SkipNode): Unit = {
    n.right match {
      case x@SkipNode(_,d,r,h) => assert(east(n) == 1 + east(x))
      case Leaf => assert(east(n) == 1)
    }
  }.ensuring(east(n.right) < east(n))


  // def subtree_size(t: Node): BigInt = {
  //   require(isSkipList(t))
  //   decreases(nodeHeight(t) + east(t))
  //   t match { 
  //     case Leaf => 0
  //     case x@SkipNode(value, down, right, h) => {
  //       assert(nodeHeight(right) <= nodeHeight(t))
  //       lem_right_east_less(x)
  //       1 + subtree_size(down) + subtree_size(right)
  //     }
  //   }
  // }
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

  
  // 1 - If sl is a skiplist, insert(sl, a) is also a skiplist ==============
//  def insertReturnsSkiplist(sl : SkipList, v: Int, height: Int): Unit = {
//    require(isSkipList(sl))
//    require(height>=0)
//    
//  } ensuring (_ => isSkipList(insert(sl,v,height)))
//
//  def insertReturnsSkiplist(n : Node, v: Int, height: Int): Unit = {
//    require(isSkipList(n))
//    require(height>=0)
//    
//  } ensuring (_ => isSkipList(insert(n,v,height)))
//  
//  // 2 - If sl is a skiplist, remove(sl, a) is also a skiplist ==============
//  def insertReturnsSkiplist(sl : SkipList, v: Int): Unit = {
//    require(isSkipList(sl))
//    
//  } ensuring (_ => isSkipList(remove(sl,v)))
//
//  def insertReturnsSkiplist(n : Node, v: Int): Unit = {
//    require(isSkipList(n))
//    
//  } ensuring (_ => isSkipList(remove(n,v)))
//
//  // 3 - If sl is a skiplist, insert(sl, a) contains a ======================
//  def insertReallyInserts(sl: SkipList, v: Int, height: Int): Unit = {
//    require(isSkipList(sl))
//    require(height>=0)
//  } ensuring (_ => isInTheList(v,insert(sl,v,height)))
//
//  def insertReallyInserts(n: Node, v: Int, height: Int): Unit = {
//    require(isSkipList(n))
//    require(height>=0)
//  } ensuring (_ => isInTheList(v,insert(n,v,height)))
//
//  // 4 - If sl is a skiplist, remove(sl, a) does not contains a =============
//  def removeReallyRemoves(sl: SkipList, v: Int): Unit = {
//    require(isSkipList(sl))
//  } ensuring (_ => !isInTheList(v,remove(sl,v)))
//
//  def removeReallyRemoves(n: Node, v: Int): Unit = {
//    require(isSkipList(n))
//  } ensuring (_ => !isInTheList(v,remove(n,v)))
//
//  // 5 - If sl is a skiplist and b is in sl, insert(sl, a) contains b =======
//  def insertDoesNotRemoveElements(sl: SkipList, a: Int, height: Int, b: Int): Unit = {
//    require(isSkipList(sl))
//    require(height>=0)
//    require(isInTheList(b,sl))
//  } ensuring (_ => isInTheList(b,insert(sl,a,height)))
//
//  def insertDoesNotRemoveElements(n: Node, a: Int, height: Int, b: Int): Unit = {
//    require(isSkipList(n))
//    require(height>=0)
//    require(isInTheList(b,n))
//  } ensuring (_ => isInTheList(b,insert(n,a,height)))
//
//  // 6 - If sl is a skiplist and b is in sl, remove(sl, a != b) contains b ===
//  def removeDoesNotRemoveOtherElements(sl: SkipList, a: Int, b: Int): Unit = {
//    require(isSkipList(sl))
//    require(isInTheList(b,sl))
//  } ensuring (_ => isInTheList(b,remove(sl,a)))
//  
//  def removeDoesNotRemoveOtherElements(n: Node, a: Int, b: Int): Unit = {
//    require(isSkipList(n))
//    require(isInTheList(b,n))
//  } ensuring (_ => isInTheList(b,remove(n,a)))
//
//  // 7 - If sl is a skiplist and a is in sl, search(sl, a) returns Some(a) ===
//  def searchFindsElement(sl: SkipList, v: Int): Unit = {
//    require(isSkipList(sl))
//    require(isInTheList(v,sl))
//  } ensuring (_ => search(sl,v) == Some(v))
//
//  def searchFindsElement(n: Node, v: Int): Unit = {
//    require(isSkipList(n))
//    require(isInTheList(v,n))  
//    n match {
//      case Leaf => ()
//      case SkipNode(value, down, right, height) => {
//        if(isValueInRightSubtree(v, right)){
//          (assume(isValueInRightSubtree(v, right)))
//        } else {
//          assume(isInTheList(v,down))
//
//        }
//      }
//    }
//  } ensuring (_ => search(n,v) == Some(v))

  // 8 - If sl is a skiplist and a is not in sl, search(sl, a) returns None ==
//  def searchFindsNone(sl: SkipList, v: Int): Unit = {
//    require(isSkipList(sl))
//    require(!isInTheList(v,sl))
//  } ensuring (_ => search(sl,v) == None())

//  def searchFindsNone(n: Node, v: Int): Unit = {
//    require(isSkipList(n))
//    require(!isInTheList(v,n))
//    n match {
//      case Leaf => ()
//      case SkipNode(value, down, right, height) => {
//        assert(value != v)
//        assert(!isValueInRightSubtree(v, right))
//        assume(!isInTheList(v,right))
//          searchFindsNone(down,v)
//          searchFindsNone(right,v)
//      }
//    }
//  } ensuring (_ => search(n,v) == None())

  //_________________________________________________________LEMMAS____________________________________________________
  
  // Lemmas for 8
  

  
  
  
  
  
  
  
  
  def elementOfSkipListIsSkipList(t: SkipNode): Unit = { // Is not used in proofs, but keep it there to make sure we don't break SkipList axioms
  require(isSkipList(t))
  assert(levelsAxiom(t.down))
  assert(levelsAxiom(t.right))
  } ensuring (_ => isSkipList(t.down) && isSkipList(t.right))


  // Proof of maxHeightIsMaxHeight for both nodes and skiplists
  def hasUpperBoundedHeight(maxHeight: Int, t: Node) = t match {
    case SkipNode(_, _, _, height) => height <= maxHeight
    case Leaf => true
  }

  def downAndRightHaveUpperBoundedHeight(maxHeight: Int, t: Node) = t match {
    case SkipNode(_, d, r, height) => height <= maxHeight && hasUpperBoundedHeight(maxHeight, d) && hasUpperBoundedHeight(maxHeight, r)
    case Leaf => true 
  }

  def heightIsLessThanMaxHeight(maxHeight: Int, t: Node): Unit = {
    require(isSkipList(t))
    require(hasUpperBoundedHeight(maxHeight, t))
  } ensuring (_ => downAndRightHaveUpperBoundedHeight(maxHeight, t))

  def maxHeightIsMaxHeight(maxHeight: Int, t: Node): Boolean = t match {
    case SkipNode(_, down, right, height) => (
      height <= maxHeight && 
      maxHeightIsMaxHeight(maxHeight, down) &&
      maxHeightIsMaxHeight(maxHeight, right)
    )
    case Leaf => true
  }

  def maxHeightIsMaxHeightLemma(maxHeight: Int, t: SkipNode): Unit = {
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


  @extern
  def assume(b: Boolean): Unit = {
    (??? : Unit)
  } ensuring (_ => b)


  // Auxiliary functions
  def isSkipNode(n: Node): Boolean = n match {case _ => true; case Leaf => false}
  def isLeaf(n: Node): Boolean = !isSkipNode(n)

  def size(t: Node): BigInt = t match {
    case SkipNode(value, down, right, height) => 1 + size(down) + sizeRight(right)
    case Leaf => 0
  }

  def sizeRight(t: Node): BigInt = t match {
    case SkipNode(value, down, right, height) => 1 + sizeRight(right)
    case Leaf => 0
  }

  def isValueInRightSubtree(target: Int, of: Node): Boolean = {
    of match {
      case Leaf => false
      case SkipNode(vOf, _, rOf, _) => {
        (target == vOf) || isValueInRightSubtree(target, rOf)
      }
    }
  }
  
  def isInTheList(target : Int, of : Node): Boolean = of match {
    case SkipNode(value, down, right, height) => isValueInRightSubtree(target,of) || isInTheList(target,down)
    case Leaf => false
  }

  //def isInTheListImpliesisInTheListDown(target : Int, of : SkipNode): Unit = {
  //  require(isSkipList(of))
  //  require(isInTheList(target,of))
  //  require(of.height>=1)
  //  if(isInRightSubtree(x, n))
  //  assert(of.down.isInstanceOf[SkipNode])
  //  of.right match {
  //    case a@SkipNode(v,d,r,h) => {
  //      lowerLevelIsSupersetofHigherOne(a,of)
  //    }
  //    case Leaf => ()
  //  }
  //} ensuring (_ => (isInTheList(target,of.down)))
//  def isNotInTheListImpliesNotInRightSubList(target : Int, of : SkipNode): Unit = {
//    require(isSkipList(of))
//    require(!isInTheList(target,of))
//    assert(!isValueInRightSubtree(target,of))
//    assert(!isValueInRightSubtree(target,of.right))
//    isInTheList(target,of.right)
//    assert(!isInTheList(target,of.down))
//    of.right match {
//      case Leaf => ()
//      case SkipNode(value, down, right, height) => assert(!isInTheList(target,down))
//    }
//
//  } ensuring (_ => (!isInTheList(target,of.right)))

  def isInTheList(target : Int, of : SkipList): Boolean = {
    return isValueInRightSubtree(target,of.head)
  }

  //‡def higherLevelIsSubsetofLowerOneValue(v : Int, n: SkipNode): Unit = {
  //‡  require(isSkipList(n))
  //‡  require(isValueInRightSubtree(v, n))
  //‡  n.right match {
  //‡    case r@SkipNode(value, _, _, _) => {
  //‡      if(value == v){
  //‡        ()
  //‡      }
  //‡      higherLevelIsSubsetofLowerOneValue(v, r)
  //‡      (r.down, n.down) match {
  //‡        case (rD@SkipNode(_, _, _, _), nD@SkipNode(_, _, _, _)) => isInRightSubtreeTransitiveValue(nD, rD, v)
  //‡        case _ => ()
  //‡      }
  //‡    }
  //‡  }
  //‡} ensuring (_ => isValueInRightSubtree(v, n.down))


//  def isInRightSubtreeTransitiveValue(n1: SkipNode, n2: SkipNode, n3: Int): Unit = {
//    require(isSkipList(n1))
//    require(isInRightSubtree(n2, n1))
//    require(isValueInRightSubtree(n3, n2))
//    n2.right match {
//      case Leaf => assume(isValueInRightSubtree(n3, n1))  
//      case n2R@SkipNode(value, down, right, height) => {
//        if (n3 != value){
//          rightIsAlsoInRightSubtree(n1, n2)
//          //isInRightSubtreeTransitiveValue(n1, n2R, n3)
//          assume(isValueInRightSubtree(n3, n1))
//        } else {
//          rightIsAlsoInRightSubtree(n1, n2)
//          assert(isInRightSubtree(n2R, n1))
//          assert(isValueInRightSubtree(value,n1))
//          assert(value == n3)
//        }
//      }
//    }
//
//  } ensuring (_ => isValueInRightSubtree(n3, n1))
//
  // Auxiliary lemmas used to validate SkipList methods
  def newDownReturnsValidElement(t: Node, v: Int): Unit = {
    require(isSkipList(t))
    t match {
      case t@SkipNode(value, _, right, _) => {
        if (value != v) {
          newDownReturnsValidElement(right, v)
        }
      }
      case Leaf => ()
    }
  } ensuring (_ => isSkipList(findNewDown(t, v)))


  //_________________________________________________________TESTING___________________________________________________


  // @ignore
  // def printList(sl: SkipList): Unit = {
  //   def printLevel(t: Node): Unit = t match {
  //     case Leaf => println("+inf]")
  //     case SkipNode(value, down, right, height) => {
  //       if (value == Int.MinValue) {
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
  // def randomAction(rd: Random, sl: SkipList, upperBoundElems: Int): SkipList = {
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