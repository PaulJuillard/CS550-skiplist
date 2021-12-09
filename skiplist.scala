import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._

object SkipList {
  sealed abstract class Node
  case class SkipList(head: Node, maxHeight:BigInt)
  case class SkipNode(value:BigInt, down: Node, right: Node, height:BigInt) extends Node
  case object Leaf extends Node
  
  def search_(t: Node, target:BigInt): Option[BigInt] = t match {
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
  def search(sl: SkipList, target:BigInt): Option[BigInt] = {
    search_(sl.head, target)
  }


  /*
  def insert(t: Node, k:BigInt, insertHeight:BigInt): Node = {
    require(isSkipList(t))
    require(insertHeight >= 0)
    require(size(t) >= 0)
    decreases(size(t))
    t match { // Returns the list with k inserted
      case sn@SkipNode(value, down, right, height) => {
        if (height > insertHeight) { // We are too high, recurse on lower level
          sizeIsNonNegative(down)
          sizeDecreasesDown(sn)
          elementOfSkipListIsSkipList(sn)
          SkipNode(value, insert(down, k, insertHeight), right, height)
        }
        else { //at correct level, insert lower, then insert right
          sizeIsNonNegative(down)
          sizeDecreasesDown(sn)
          val lowerLeftmostNode = insert(down, k, insertHeight)
          assert(isRight(lowerLeftmostNode, k))
          assert(isSkipList(lowerLeftmostNode))

          insertRight(t, k, lowerLeftmostNode) //insert right need new underlying level to update links to down nodes
        }
      }
      case Leaf => Leaf // Found a leaf (we are at level -1)
    }
  }
  */
  //leftmost element from level
  def levelLeft(t: Node, level:BigInt): Node = {
    require(isSkipList(t))
    // TODO require(nodeHeight(t) >= level)
    t match {
      case sn@SkipNode(_,down,_,height) =>
        if(height > level) levelLeft(down, level)
        else sn
      case Leaf => Leaf //NOTE this should not happen when calling insertLevelUp
    }
  }//.ensuring(_ => ret isInstanceOf(SkipNode)))

  def insertLevelUp(k:BigInt, desiredHeight:BigInt, topLeft : Node, level:BigInt, lowerLevelLeft: Node): Node = {
    // insertRight in level 0 to maxHeight
    // if desiredHeight is lower then level, just update links to the new subtree
    require(isSkipList(topLeft))
    require(isSkipList(lowerLevelLeft))
    require(desiredHeight >= 0)
    require(level >= 0)
    // TODO decreases(nodeHeight(topLeft) - level)
    topLeft match {
      case topleft@SkipNode(_,_,_,_) =>
        val level_leftmost = levelLeft(topLeft, level)
        val newLevelLeft = insertRight(level_leftmost, k, desiredHeight, lowerLevelLeft)
        assert(isRight(newLevelLeft,k)) //TODO
        if(level < topleft.height) insertLevelUp(k, desiredHeight, topLeft, level+1, newLevelLeft)
        else newLevelLeft
      
      case Leaf => Leaf //NOTE this should not happen
    }
  }// .ensuring(_ => if(level < desiredHeight) isIn(newLevelLeft, k)) TODO

  def isRight(t: Node, v:BigInt): Boolean = {
    require(isSkipList(t))
    assert(hasNonNegativeHeight(t))
    //decreases(size(t))
    t match {
      case SkipNode(value,_,r,h) =>
        if(v == value) true
        else {
          isRight(r,v)
        }
      case Leaf => false
    }
  }

  //proves that if newDown contains k, it returns a skipnode of value k
  def newDownReturnsNode(t: Node, v :BigInt): Unit = {
    require(isSkipList(t))
    require(size(t) >= 0)
    require(isRight(t, v))
    decreases(size(t))
    t match {
      case sn@SkipNode(value, _, r, h) =>
        if(v == value) assert(findNewDown(sn, v) == sn)
        else {
          assert(isRight(r,v))
          assert(r.isInstanceOf[SkipNode])
          r match {
           case sn2@SkipNode(_,_,_,_) =>
             sizeSkipNodeIsPositive(sn2)
            case Leaf => ()
          }
          sizeDecreasesToTheRight(sn)
          newDownReturnsNode(r, v)
        }
      case Leaf => ()
    }
  }.ensuring(_=> findNewDown(t, v).isInstanceOf[SkipNode]) //and SkipNode(v,_,_,h)

  //NOTE lowerlevel is the new node under t with inserted value k
  // we need to update all links
  def insertRight(t: Node, k:BigInt, desiredHeight:BigInt, lowerLevel: Node): Node = {
    require(isSkipList(t))
    require(isSkipList(lowerLevel))
    require(size(t) >= 0)
    require(nodeHeight(lowerLevel) < nodeHeight(t))
    require(isRight(lowerLevel, k))
    decreases(size(t))
    t match {
      case sn@SkipNode(value, down, right, height) => {
        val newDown = findNewDown(lowerLevel, value) // down node to update link with
        newDownReturnsValidElement(lowerLevel, value)
        assert(isSkipList(newDown))
        //assert(lowerLevelIsSupersetofHigherOne(t,lowerLevel)) 
        assert(isRight(lowerLevel, value))
        newDownReturnsNode(lowerLevel, value)
        assert(nodeHeight(newDown) == nodeHeight(lowerLevel)) //TODO wrong if k not in lowerlevel, maybe use levels
        right match {
          case SkipNode(valueR, downR, rightR, heightR) => {
            if ((desiredHeight < height) || //dont need to insert anymore
                (valueR <= k) || //insert is further right
                (value >= k)) {  //passed the insertion point
              // simply update down
              sizeDecreasesToTheRight(sn)
              sizeIsNonNegative(right)
              //update link down with newdown
              //recurse right
              val ret = SkipNode(value, newDown, insertRight(right, k, desiredHeight, newDown), height)
              assert(isSkipList(ret))
              ret
            }
            else {
              // Insert to the right
              val insertedDown = findNewDown(lowerLevel, k) //inserted node at lowerlevel, which must be insertedNode.down
              //precondition checks
              sizeDecreasesToTheRight(sn)
              sizeIsNonNegative(right)
              val newRight = insertRight(right, k, desiredHeight, newDown) //keep going right to update down links
              val insertedNode = SkipNode(k, insertedDown, newRight, height)
              val ret = SkipNode(value, newDown, insertedNode, height)
              assert(isSkipList(ret))
              ret
            }
          }
          case Leaf => { // Reached end of list, 
            if (value < k && desiredHeight <= height) { // we need to insert to the right
              val insertedDown = findNewDown(lowerLevel, k) //inserted node at lowerlevel, which must be insertedNode.down
              val insertedNode = SkipNode(k, insertedDown, Leaf, height)
              val ret = SkipNode(value, newDown, insertedNode, height)
              //assert(isSkipList(ret))
              ret
            }
            else { // Just update down
              val ret = SkipNode(value, newDown, Leaf, height)
              assert(nodeHeight(newDown) == nodeHeight(lowerLevel))
              assert(heightDecreasesDown(ret)) //TODO
              assert(isSkipList(ret))
              ret
            }
          }
        }
      }
      case Leaf => Leaf
    }
  }

  // boil node up to level newHeight
  def increaseHeight(t: Node, newHeight:BigInt): Node = {
    require(isSkipList(t))
    //TODO decreases(newHeight - nodeHeight(t))
    t match {
      case SkipNode(value, down, right, height) => 
        if (height >= newHeight) {
          t
        } 
        else {
          increaseHeight(SkipNode(value, t, Leaf, height+1), newHeight)
        }
      case Leaf => Leaf
    }
  }

  def insert(sl: SkipList, k:BigInt, height:BigInt): SkipList = {
    require(isSkipList(sl))
    require(height >= 0)
    // if needed, bring first value to same height
    val newHead = increaseHeight(sl.head, height)
    assert(isSkipList(newHead))
    SkipList(insertLevelUp(k, height, newHead, 0, Leaf), max(sl.maxHeight, height))
  } 

  /*
  def
  insert(sl: SkipList, k:BigInt): SkipList = {
     if (isIn(sl, k)) {
       sl
     }
     def getRandomLevel(rd: Random, acc:BigInt):BigInt = {if (rd.nextInt(2) == 0) {acc} else {getRandomLevel(rd, acc+1)}}
     val r = new Random
     val height = getRandomLevel(r, 0)
     //println("random height : " + height)
     insert(sl, k, height)
  }
  */

  def findNewDown(t: Node, v:BigInt): Node = t match {
    case SkipNode(value, down, right, height) => 
      if (value == v) {t} 
      else {findNewDown(right, v)}
    case Leaf => Leaf
  }

  /*
  def remove(sl: SkipList, k:BigInt): SkipList = {
    require(isSkipList(sl))
    require(k !=BigInt.MinValue)
    sizeIsNonNegative(sl.head)
    SkipList(remove(sl.head, k), sl.maxHeight)
  }

  def remove(t: Node, k:BigInt): Node = {
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
  
  def removeRight(t: Node, k:BigInt, lowerLevel: Node): Node = {
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
  def isIn(sl: SkipList, k:BigInt): Boolean = {
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
      value == BigInt(Int.MinValue) && 
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
        if(isValueInRightSubtree(v, right)){
          (assume(isValueInRightSubtree(v, right)))
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
        assert(!isValueInRightSubtree(v, right))
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

  def isValueInRightSubtree(target:BigInt, of: Node): Boolean = {
    of match {
      case Leaf => false
      case SkipNode(vOf, _, rOf, _) => {
        (target == vOf) || isValueInRightSubtree(target, rOf)
      }
    }
  }
  
  def isInTheList(target :BigInt, of : Node): Boolean = of match {
    case SkipNode(value, down, right, height) => isValueInRightSubtree(target,of) || isInTheList(target,down)
    case Leaf => false
  }

  //def isInTheListImpliesisInTheListDown(target :BigInt, of : SkipNode): Unit = {
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
//  def isNotInTheListImpliesNotInRightSubList(target :BigInt, of : SkipNode): Unit = {
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

  def isInTheList(target :BigInt, of : SkipList): Boolean = {
    return isValueInRightSubtree(target,of.head)
  }

  //‡def higherLevelIsSubsetofLowerOneValue(v :BigInt, n: SkipNode): Unit = {
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


//  def isInRightSubtreeTransitiveValue(n1: SkipNode, n2: SkipNode, n3:BigInt): Unit = {
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
  def newDownReturnsValidElement(t: Node, v:BigInt): Unit = {
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
    assert(nD.isInstanceOf[SkipNode])
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