import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._


object SkipList {
  sealed abstract class Node
  case class SkipList(head: Node, maxHeight: Int)
  case class SkipNode(value: Int, down: Node, right: Node, height: Int) extends Node
  case object Leaf extends Node
  
  // def search(sl: SkipList, target: Int): Option[Int] = {
  //   def search_(t: Node, target: Int): Option[Int] = t match {
  //     case SkipNode(v,d,r,_) =>
  //         if (v == target) { 
  //           Some(v) 
  //         }
  //         else {
  //           r match {
  //             case SkipNode(vR,_,_,_) => 
  //               if (vR <= target) { // If value is somewhere to the right, go right
  //                 search_(r, target)
  //               }
  //               else { // If not, try down
  //                 search_(d, target)
  //               }
  //             case Leaf => search_(d, target) // Reached the end of this level, go down
  //           }
  //         }
  //     case Leaf => None()
  
  //   }
  //   search_(sl.head, target)
  // }

  // def insert(sl: SkipList, k: Int, height: Int): SkipList = {
  //   require(height>=0)
  //   val newHeight = min(sl.maxHeight + 1, height) // TODO : Check that this makes sense

  //   def insert_(t: Node, k: Int, insertHeight: Int): Node = t match { // Returns the list with k inserted
  //     case SkipNode(value, down, right, height) => {
  //       if (height > insertHeight) { // We are too high, recurse on lower level
  //         SkipNode(value, insert_(down, k, insertHeight), right, height)
  //       }
  //       else {
  //         val lowerLeftmostNode = insert_(down, k, insertHeight)
  //         insertRight(t, k, lowerLeftmostNode)
  //       }
  //     }
  //     case Leaf => Leaf // Found a leaf (we are at level -1)
  //   }

  //   def insertRight(t: Node, k: Int, lowerLevel: Node): Node = t match {
  //     case SkipNode(value, down, right, height) => {
  //       val newDown = findNewDown(lowerLevel, value)
  //       right match {
  //         case SkipNode(valueR, downR, rightR, heightR) => {
  //           if ((valueR <= k) || (value >= k)) { // Key must be inserted further to the right, or we have passed the insertion point, simply update down
  //             SkipNode(value, newDown, insertRight(right, k, newDown), height)
  //           }
  //           else { // Insert to the right
  //             val insertedNode = SkipNode(k, Leaf, right, height) 
  //             SkipNode(value, newDown, insertRight(insertedNode, k, newDown), height)
  //           }
  //         }
  //         case Leaf => { // Reached end of list, we insert to the right if the current value is less than k
  //           if (value < k) { // Insert to the right
  //             val insertedNode = SkipNode(k, Leaf, Leaf, height) 
  //             SkipNode(value, newDown, insertRight(insertedNode, k, newDown), height)
  //           }
  //           else { // Just update down
  //             SkipNode(value, newDown, Leaf, height)
  //           }
  //         }
  //       }
  //     }
  //     case Leaf => Leaf
  //   }

  //   def increaseHeight(t: Node, newHeight: Int): Node = {
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

  //   SkipList(insert_(increaseHeight(sl.head, newHeight), k, newHeight), max(sl.maxHeight, height)) 
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

  // def findNewDown(t: Node, v: Int): Node = t match {
  //   case SkipNode(value, down, right, height) => if (value == v) {t} else {findNewDown(right, v)}
  //   case Leaf => Leaf
  // }

  // def remove(sl: SkipList, k: Int): SkipList = {
  //   require(isSkipList(sl))
  //   require(k != Int.MinValue)
  //   def remove_(t: Node, k: Int): Node = {
  //     require(isSkipList(t))
  //     decreases(size(t))
  //     t match { // Returns the list with k removed
  //       case SkipNode(value, down, right, height) => {
  //         val lowerLeftmostNode = remove_(down, k)
  //         removeRight(t, k, lowerLeftmostNode)
  //       }
  //       case Leaf => Leaf // Found a leaf (we are at level -1)
  //     }
  //   }

  //   def removeRight(t: Node, k: Int, lowerLevel: Node): Node = {
  //     require(isSkipList(t))
  //     require(isSkipList(lowerLevel))
  //     decreases(size(t))
  //     t match {
  //       case SkipNode(value, down, right, height) => {
  //         val newDown = findNewDown(lowerLevel, value)
  //         right match {
  //           case SkipNode(valueR, downR, rightR, heightR) => {
  //             if (valueR == k) { // Remove right
  //               assert(size(right) < size(t))
  //               val hope = removeRight(rightR, k, newDown)
  //               SkipNode(value, newDown, hope, height)
  //             }
  //             else { // Value is not the next node, just recurse to the right
  //               val hope = removeRight(right, k, newDown)
  //               SkipNode(value, newDown, hope, height)
  //             }
  //           }
  //           case Leaf => SkipNode(value, newDown, Leaf, height) // Reached end of this level, just update lower node
  //         }
  //       }
  //       case Leaf => Leaf
  //     }
  //   }

  //   SkipList(remove_(sl.head, k), sl.maxHeight)
  // }

  
  // def isIn(sl: SkipList, k: Int): Boolean = {
  //   search(sl, k) match {
  //     case None() => false
  //     case Some(value) => true
  //   }
  // }

  def size(t: Node): BigInt = t match {
    case SkipNode(value, down, right, height) => 1 + size(down) + sizeRight(right)
    case Leaf => 0
  }

  def sizeRight(t: Node): BigInt = t match {
    case SkipNode(value, down, right, height) => 1 + sizeRight(right)
    case Leaf => 0
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
  def hasNonNegativeHeight(node : Node): Boolean = {
    node match {
      case SkipNode(v,d,r,h) => h >= 0 && hasNonNegativeHeight(d) && hasNonNegativeHeight(r)
      case Leaf => true 
    }
  }

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

  def isInRightSubtree(target: Node, of: Node): Boolean = {
    (target, of) match {
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

  def headIsMinInt(sl: SkipList) = sl.head match {
    case Leaf => false
    case SkipNode(value, down, right, height) => (
      value == Int.MinValue && 
      sl.maxHeight >= 0 && 
      height <= sl.maxHeight
    )
  }

  def isSkipList(sl: SkipList): Boolean = {
    if (!headIsMinInt(sl)) {false}
    else if (hasNonNegativeHeight(sl.head)) {
      heightDecreasesDown(sl.head) && increasesToTheRight(sl.head) && levelsAxiom(sl.head)
    }
    else {false}
  }

  def isSkipList(t: Node): Boolean = {
    if (hasNonNegativeHeight(t)) {
      heightDecreasesDown(t) && increasesToTheRight(t) && levelsAxiom(t)
    }
    else {false}
  }



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
  //_________________________________________________INVARIANTS__________________________________________
  // Invariants : 
  // If sl is skiplist and insert element then result is also skiplist and search returns Some(x)
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
  //_________________________________________________________LEMMAS____________________________________________________
  def elementOfSkipListIsSkipList(t: SkipNode): Unit = {
    require(isSkipList(t))
    assert(levelsAxiom(t.down))
    assert(levelsAxiom(t.right))
  } ensuring (_ => isSkipList(t.down) && isSkipList(t.right))

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

  def sizeSkipNodeIsPositive(t: SkipNode): Unit = {
    sizeIsNonNegative(t.down)
    sizeRightIsNonNegative(t.right)
  } ensuring (_ => size(t) > 0)

  // def sizeOfRightIsLower(t: SkipNode) = { // TODO : Times out
  //   require(isSkipList(t))
  //   t.right match {
  //     case Leaf => {
  //       sizeSkipNodeIsPositive(t)
  //       assert(size(t.right) == 0)
  //     }
  //     case SkipNode(value, down, right, height) => {
  //       assert(1 + size(down) + sizeRight(right) > size(right))
  //     }
  //   }
  // }.ensuring(_ => size(t) > size(t.right))

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

  def isSkipNode(n: Node): Boolean = n match {case _ => true; case Leaf => false}
  def isLeaf(n: Node): Boolean = !isSkipNode(n)

  def ifNodeHasDownAllRightNodesHaveDown(n: SkipNode, x: SkipNode): Unit = {
    require(isSkipList(n))
    require(isSkipList(x))
    require(isInRightSubtree(x, n))
    require(isSkipNode(n.down))
  } ensuring (_ => isSkipNode(x.down))

  def ifSkipNodeInRightSubtreeRightIsNotLeaf(n: SkipNode, x: SkipNode): Unit = {
    require(isSkipList(n))
    require(isSkipList(x))
    require(isInRightSubtree(x, n))
  } ensuring (_ => isSkipNode(n.right))

  def rightIsAlsoInRightSubtree(n: SkipNode, x: SkipNode): Unit = { // TODO : Times out
    require(isSkipList(n))
    require(isSkipList(x))
    require(isInRightSubtree(x, n))
  } ensuring (_ => isInRightSubtree(x.right, n))

  def isInRightSubtreeTransitive(n1: SkipNode, n2: SkipNode, n3: SkipNode): Unit = {
    require(isSkipList(n1))
    require(isSkipList(n2))
    require(isSkipList(n3))
    require(isInRightSubtree(n2, n1))
    require(isInRightSubtree(n3, n2))
    assert((n2 == n3) || isInRightSubtree(n3, n2.right)) // TODO : Times out
    if (n3 != n2) {
      rightIsAlsoInRightSubtree(n1, n2)
      n2.right match {
        case n2R@SkipNode(_, _, _, _) => isInRightSubtreeTransitive(n1, n2R, n3)
        case Leaf => ()
      }
    }
  } ensuring (_ => isInRightSubtree(n3, n1))

  def levelsLemma(n: SkipNode, x: SkipNode): Unit = { // TODO : Times out
    require(isSkipList(n))
    require(isSkipList(x))
    require(isInRightSubtree(x, n))
  } ensuring (_ => isInRightSubtree(x.down, n.down))


  //_________________________________________________________TESTING___________________________________________________

/*
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