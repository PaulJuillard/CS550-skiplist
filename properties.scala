package users
import users.skiplist._
import users.utils._
import users.proofs._

import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._

package object properties {
  // Def - Element is in the list if it is in the right subtree of first element, or in the list of element just below
  // 0 - If sl is a skiplist and a is in the right subtree of node, then a.down is in the right subtree of node.down (and a.down.value == a.value)
  // 1 - If sl is a skiplist, insert(sl, a) is also a skiplist
  // 2 - If sl is a skiplist, remove(sl, a) is also a skiplist (NOT PROVEN)
  // 3 - If sl is a skiplist, insert(sl, a) contains a
  // 4 - If sl is a skiplist, remove(sl, a) does not contain a (NOT PROVEN)
  // 5 - If sl is a skiplist and b is in sl, insert(sl, a) contains b (NOT PROVEN)
  // 6 - If sl is a skiplist and b is in sl, remove(sl, a != b) contains b (NOT PROVEN)
  // 7 - If sl is a skiplist and a is in sl, search(sl, a) returns Some(a)
  // 8 - If sl is a skiplist and a is not in sl, search(sl, a) returns None
  
  // 0
  def higherLevelIsSubsetofLowerOne(n: SkipNode, x: SkipNode): Boolean = {
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
    (n.down.isLeaf && x.down.isLeaf) || isInRightSubtree(x.down, n.down)
  }.holds

  def higherLevelIsSubsetofLowerOne(v: Int, n: SkipNode): Boolean = {
    require(n.isSkipList)
    require(isInRightSubtree(v, n))
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
    n.down.isLeaf || isInRightSubtree(v, n.down)
  }.holds

  // 1
  def insertReturnsSkiplist(sl : SkipList, v: Int, height:BigInt): Boolean = {
    require(sl.isSkipList)
    require(height>=0)
    insert(sl,v,height).isSkipList
  }.holds
  
  // 3
  def insertReallyInserts(sl: SkipList, v:Int, height:BigInt): Boolean = {
    require(sl.isSkipList)
    require(height>=0)
    val inserted = insert(sl,v,height)
    isInTheList(v,inserted)
  }.holds

  // 7
  def searchFindsElement(sl: SkipList, v: Int): Boolean = {
    require(sl.isSkipList)
    require(isInTheList(v,sl))
    searchFindsElement(sl.head,v)
    search(sl,v) == Some(v)
  }.holds

  def searchFindsElement(n: Node, v:Int): Boolean = {
    require(n.isSkipList)
    require(isInTheList(v,n)) 
    decreases(size(n))
    n match {
      case Leaf => ()
      case n@SkipNode(value, down, right, height) => {
        if (value != v) {
          right match {
            case r@SkipNode(vR,_,_,_) => {
              if (vR <= v){
                lem_isInTheListLargerThanNodeImpliesInRightsList(v,n)
                lem_sizeDecreasesToTheRight(n)
                searchFindsElement(r,v)
              } else {
                lem_isInRightSubtreeImpliesValueHigher(v,r)
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
    search_(n,v) == Some(v)
  }.holds

  // 8
  def searchFindsNone(sl: SkipList, v: Int): Boolean = {
    require(sl.isSkipList)
    require(!isInTheList(v,sl))
    searchFindsNone(sl.head,v)
    search(sl,v) == None()
  }.holds
  

  def searchFindsNone(n: Node, v: Int): Boolean = {
    require(n.isSkipList)
    require(!isInTheList(v,n))
    decreases(size(n))
    n match {
      case Leaf => ()
      case n@SkipNode(value, d, r, _) => {
        r match {
          case r@SkipNode(vR,_,_,_) => 
            if (vR <= v) { 
                lem_sizeDecreasesToTheRight(n)
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
    search_(n,v) == None()
  }.holds
}