package users
import users.skiplist._
import users.utils._
import users.proofs._

import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

package object properties {
  // __________________________________________PROPERTIES DOC__________________________________________
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

  // 1 - If sl is a skiplist, insert(sl, a) is also a skiplist ==============
  def insertReturnsSkiplist(sl : SkipList, v: Int, height:BigInt): Unit = {
    require(sl.isSkipList)
    require(height>=0)
  } ensuring (_ => insert(sl,v,height).isSkipList)
  
  // def insertReturnsSkiplist(n : Node, v: Int, height:BigInt): Unit = {
  //   require(n.isSkipList)
  //   require(height>=0)
  //   
  // } ensuring (_ => insert(n,v,height).isSkipList)
    
    /*
  // 2 - If sl is a skiplist, remove(sl, a) is also a skiplist ==============
  def insertReturnsSkiplist(sl : SkipList, v:BigInt): Unit = {
    require(isSkipList(sl))
    
  } ensuring (_ => isSkipList(remove(sl,v)))

  def insertReturnsSkiplist(n : Node, v:BigInt): Unit = {
    require(isSkipList(n))
    
  } ensuring (_ => isSkipList(remove(n,v)))
  */
  // 3 - If sl is a skiplist, insert(sl, a) contains a ======================
  def insertReallyInserts(sl: SkipList, v:Int, height:BigInt): Boolean = {
    require(sl.isSkipList)
    require(height>=0)
    val inserted = insert(sl,v,height)
    isInTheList(v,inserted)
  }.holds
  /*
  def insertReallyInserts(n: Node, v:BigInt, height:BigInt): Unit = {
    require(isSkipList(n))
    require(height>=0)
    val inserted = insert(sl, v, height)
    val bottomLeft = levelLeftmost(inserted, 0)
    assert(isInRightSubtree(v, bottomLeft))
  } ensuring (_ => isInTheList(v,insert(n,v,height)))
  
  // 4 - If sl is a skiplist, remove(sl, a) does not contains a =============
  def removeReallyRemoves(sl: SkipList, v:BigInt): Unit = {
    require(isSkipList(sl))
  } ensuring (_ => !isInTheList(v,remove(sl,v)))

  def removeReallyRemoves(n: Node, v:BigInt): Unit = {
    require(isSkipList(n))
  } ensuring (_ => !isInTheList(v,remove(n,v)))
  */
  // 5 - If sl is a skiplist and b is in sl, insert(sl, a) contains b =======
  def insertDoesNotRemoveElements(sl: SkipList, a: Int, height:BigInt, b:Int): Unit = {
    require(sl.isSkipList)
    require(height>=0)
    require(isInTheList(b,sl))
  } ensuring (_ => isInTheList(b,insert(sl,a,height)))
  /*
  // 6 - If sl is a skiplist and b is in sl, remove(sl, a != b) contains b ===
  def removeDoesNotRemoveOtherElements(sl: SkipList, a:BigInt, b:BigInt): Unit = {
    require(isSkipList(sl))
    require(isInTheList(b,sl))
  } ensuring (_ => isInTheList(b,remove(sl,a)))
  
  def removeDoesNotRemoveOtherElements(n: Node, a:BigInt, b:BigInt): Unit = {
    require(isSkipList(n))
    require(isInTheList(b,n))
  } ensuring (_ => isInTheList(b,remove(n,a)))
  */
  // 7 - If sl is a skiplist and a is in sl, search(sl, a) returns Some(a) ===
  /*
  def searchFindsElement(sl: SkipList, v: Int): Unit = {
    require(sl.isSkipList)
    require(isInTheList(v,sl))
    searchFindsElement(sl.head,v)
  } ensuring (_ => search(sl,v) == Some(v))

  def searchFindsElement(n: Node, v:Int): Unit = {
    require(n.isSkipList)
    require(isInTheList(v,n)) 
    decreases(size(n))
    n match {
      case Leaf => ()
      case n@SkipNode(value, down, right, height) => {
        if (value == v){
          assert(search_(n,v) == Some(v))
        }
        else {
          right match {
            case r@SkipNode(vR,_,_,_) => {
              if (vR <= v){
                lem_isInTheListLargerThanNodeImpliesInRightsList(v,n)
                assert(isInTheList(v,r))
                sizeDecreasesToTheRight(n)
                searchFindsElement(r,v)
              } else {
                assert(v<vR)
                lem_isInRightSubtreeImpliesValueHigher(v,r)
                lem_isInTheListButNotInRightsImpliesDownIsASkipnode(v,n)
                down match {
                  case d@SkipNode(vD, _, _, _) => {
                    lem_isInTheListImpliesInTheListOfDown(v,n)
                    searchFindsElement(d,v)
                  }
                  case Leaf =>()
                }
              }
            }
            case Leaf => {
              down match {
                case d@SkipNode(vD, _, _, _) => {
                  lem_isInTheListImpliesInTheListOfDown(v,n)
                  searchFindsElement(d,v)
                }
              }
            }
          }
        }
      }
    }
  } ensuring (_ => search_(n,v) == Some(v))

// 8 - If sl is a skiplist and a is not in sl, search(sl, a) returns None ==
  def searchFindsNone(sl: SkipList, v: Int): Unit = {
    require(sl.isSkipList)
    require(!isInTheList(v,sl))
    searchFindsNone(sl.head,v)
  } ensuring (_ => search(sl,v) == None())
  

  def searchFindsNone(n: Node, v: Int): Unit = {
    require(n.isSkipList)
    require(!isInTheList(v,n))
    decreases(size(n))
    n match {
      case Leaf => ()
      case n@SkipNode(value, d, r, _) => {
        assert(value != v)
        assert(!isInRightSubtree(v, r))
        r match {
          case r@SkipNode(vR,_,_,_) => 
            if (vR <= v) { 
                sizeDecreasesToTheRight(n)
                lem_notInTheListImpliesNotInRightsList(v,n,r)
                searchFindsNone(r, v)
              }
              else {
                searchFindsNone(d, v)
              }

          case Leaf => {
            searchFindsNone(d, v)
          }
        }
      }
    }
  } ensuring (_ => search_(n,v) == None())
  */

}