import stainless.math.{max, min}
import stainless.lang._
import stainless.annotation._
import stainless.collection._


object SkipList {
  sealed abstract class Node
  case class SkipList(head: Node, max_height: Int)
  case class SkipNode(value: Int, down: Node, right: Node, height: Int) extends Node
  case object Leaf extends Node
  
  // TODO : Write invariants and make Stainless prove them
  

  def search(sl: SkipList, target: Int): Option[Int] = {
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
    search_(sl.head, target)
  }

  def insert_h(sl: SkipList, k: Int, height: Int): SkipList = {
    require(height>=0)
    val newHeight = min(sl.max_height + 1, height) // TODO : Check that this makes sense

    def insert_(t: Node, k: Int, insertHeight: Int): Node = t match { // Returns the list with k inserted
      case SkipNode(value, down, right, height) => {
        if (height > insertHeight) { // We are too high, recurse on lower level
          SkipNode(value, insert_(down, k, insertHeight), right, height)
        }
        else {
          val lowerLeftmostNode = insert_(down, k, insertHeight)
          insertRight(t, k, lowerLeftmostNode)
        }
      }
      case Leaf => Leaf // Found a leaf (we are at level -1)
    }

    def insertRight(t: Node, k: Int, lowerLevel: Node): Node = t match {
      case SkipNode(value, down, right, height) => {
        val newDown = findNewDown(lowerLevel, value)
        right match {
          case SkipNode(valueR, downR, rightR, heightR) => {
            if ((valueR <= k) || (value >= k)) { // Key must be inserted further to the right, or we have passed the insertion point, simply update down
              SkipNode(value, newDown, insertRight(right, k, newDown), height)
            }
            else { // Insert to the right
              val insertedNode = SkipNode(k, Leaf, right, height) 
              SkipNode(value, newDown, insertRight(insertedNode, k, newDown), height)
            }
          }
          case Leaf => { // Reached end of list, we insert to the right if the current value is less than k
            if (value < k) { // Insert to the right
              val insertedNode = SkipNode(k, Leaf, Leaf, height) 
              SkipNode(value, newDown, insertRight(insertedNode, k, newDown), height)
            }
            else { // Just update down
              SkipNode(value, newDown, Leaf, height)
            }
          }
        }
      }
      case Leaf => Leaf
    }

    def increaseHeight(t: Node, newHeight: Int): Node = {
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

    SkipList(insert_(increaseHeight(sl.head, newHeight), k, newHeight), max(sl.max_height, height)) 
  }

  def findNewDown(t: Node, v: Int): Node = t match {
    case SkipNode(value, down, right, height) => if (value == v) {t} else {findNewDown(right, v)}
    case Leaf => Leaf
  }

  def remove(sl: SkipList, k: Int): SkipList = {
    def remove_(t: Node, k: Int): Node = t match { // Returns the list with k removed
      case SkipNode(value, down, right, height) => {
        val lowerLeftmostNode = remove_(down, k)
        removeRight(t, k, lowerLeftmostNode)
      }
      case Leaf => Leaf // Found a leaf (we are at level -1)
    }

    def removeRight(t: Node, k: Int, lowerLevel: Node): Node = t match {
      case SkipNode(value, down, right, height) => {
        val newDown = findNewDown(lowerLevel, value)
        right match {
          case SkipNode(valueR, downR, rightR, heightR) => {
            if (valueR == k) { // Remove right
              SkipNode(value, newDown, removeRight(rightR, k, newDown), height)
            }
            else { // Value is not the next node, just recurse to the right
              SkipNode(value, newDown, removeRight(right, k, newDown), height)
            }
          }
          case Leaf => SkipNode(value, newDown, Leaf, height) // Reached end of this level, just update lower node
        }
      }
      case Leaf => Leaf
    }

    SkipList(remove_(sl.head, k), sl.max_height)
  }

  
  def isIn(sl: SkipList, k: Int): Boolean = {
    search(sl, k) match {
      case None() => false
      case Some(value) => true
    }
  }


  /* SkipList structural properties
  - max_Height >= heights >= 0

  - if(n.h > 0) n.b.height = n.height - 1 and n.val == v.b.val
  - if(n.h == 0) n.b is leaf

  - if(n.r is skipnode) n.r.v > n.r and n.r.h == n.h
  
  - skiplist.head is skipnode and skiplist.head.value = -inf
  */
  
  // Invariants : 
  // If insert element then search, found x
  // If search element in the list, it is found x
  // If remove then search, not found x
  // Every level is a subset of the level below
  // Search is probabilistically log
  // Also first element is always -inf

/*
  def inv_inserted_found(sl:SkipList, k: Int):Unit = {
    //TODO change hardcoded 0
  }.ensuring(_=> search(insert_h(sl, k, 0), k) == Some(k))

  def inv_isin_search(sl: SkipList, k: Int): Unit = {
    //can distinguish cases if needed
  }.ensuring(_=> isIn(sl, k) == (search(sl, k) == Some(k)))

  def inv_remove_notfound(sl:SkipList, k:Int) : Unit = {
  }.ensuring(_ => !isin(remove(sl, k)))
*/
  /*
  def level(sl: SkipList, h: Int): Set[Int]{
    require(h>=0)
    //go bfs
    def level(t: Node, h: Int, acc: Set[Int]): Set[Int] = t match {
      case Node(value, down, right, height) =>
        if(height > h) =>

    }
  }
  */



/*
  @ignore
  def insert(sl: SkipList, k: Int): SkipList = {
    if (isIn(sl, k)) {
      sl
    }
    def getRandomLevel(rd: Random, acc: Int): Int = {if (rd.nextInt(2) == 0) {acc} else {getRandomLevel(rd, acc+1)}}
    val r = new Random
    val height = getRandomLevel(r, 0)
    //println("random height : " + height)
    insert_h(sl, k, height)
  }
  

  @ignore
  def printList(sl: SkipList): Unit = {
    def printLevel(t: Node): Unit = t match {
      case Leaf => println("+inf]")
      case SkipNode(value, down, right, height) => {
        if (value == Int.MinValue) {
          print("[" + value + ", ")
        }
        else {
          print(value + ", ")
        }
        printLevel(right)
      }
    }
    def printList_(t: Node): Unit = t match {
      case Leaf => println()
      case SkipNode(value, down, right, height) => {printLevel(t); printList_(down)}
    }
    printList_(sl.head)
  }

  
  @ignore
  def randomAction(rd: Random, sl: SkipList, upperBoundElems: Int): SkipList = {
    val elem = rd.nextInt(upperBoundElems)
    rd.nextInt(3) match {
      case 0 => {
        println("Searching for " + elem)
        if (isIn(sl, elem)) {
          println("Found")
        }
        else {
          println("Not found")
        }
        println()
        sl
      }
      case 1 => {
        println("Inserting " + elem)
        val resultList = insert(sl, elem)
        printList(resultList)
        resultList
      }
      case 2 => {
        println("Removing " + elem)
        val resultList = remove(sl, elem)
        printList(resultList)
        resultList
      }
    }
  }

  @ignore
  def initSL(): SkipList = {
    val firstNode = SkipNode(Int.MinValue, Leaf, Leaf, 0)
    return SkipList(firstNode, 0)
  }
  @ignore
  def main(args: Array[String]): Unit = {
    val nOps = 50
    val upperBoundElems = 100
    val r = new Random
    val sl = initSL()
    (0 until nOps).foldLeft(sl)((tmpList, _) => randomAction(r, tmpList, upperBoundElems))
  }
  */
}