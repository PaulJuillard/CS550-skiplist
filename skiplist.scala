import math.{max, min}

object SkipList {  
  sealed abstract class Node
  case class SkipList(head: Node, max_height: Int)
  case class SkipNode(value: Int, down: Node, right: Node, height: Int) extends Node
  case object Leaf extends Node
  
  // TODO : Make sure first element is always -inf, and last element is always +inf (or make Stainless assume, TBD later)
  // TODO : Add an insert method without height, and determine height randomly, then call current method
  // TODO : Tests

  // TODO : Write invariants and make Stainless prove them
  // Invariants : If insert element then search, found
  // If search element in the list, it is found
  // If remove then search, not found
  // Every level is a subset of the level below
  // Search is probabilistically log

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
      case Leaf => None
    }
    search_(sl.head, target)
  }

  def insert(sl: SkipList, k: Int, height: Int): SkipList = {
    val newHeight = min(sl.max_height + 1, height) // TODO : Check that this makes sense
    def insert_(t: Node, k: Int, insertHeight: Int): (Node, Node) = t match { // Returns this node with k inserted, and the new node containing k inserted at this level
      case SkipNode(value, down, right, height) => {
        if (height > insertHeight) { // We are too high, recurse on lower level
          (SkipNode(value, insert_(down, k, insertHeight)._1, right, height), Leaf)
        }
        else {
          right match {
            case SkipNode(valueR, downR, rightR, _) => {
              if (valueR == k) {(t, t)}
              else if (valueR < k) { // keep searching to the right
                val (newRight, insertedRight) = insert_(right, k, insertHeight)
                val (newDown, _) = insert_(down, k, insertHeight)
                (SkipNode(value, newDown, newRight, height), insertedRight)
              }
              else { // Insert done here
                val (newDown, insertedDown) = insert_(down, k, insertHeight)
                val insertedRight = SkipNode(k, insertedDown, right, height)
                (SkipNode(value, newDown, insertedRight, height), insertedRight)
              }
            }
            case Leaf => { // Found a leaf to the right. Simply replace it by the new node
              val (newDown, insertedDown) = insert_(down, k, insertHeight)
              val insertedRight = SkipNode(k, insertedDown, right, height)
              (SkipNode(value, newDown, insertedRight, height), insertedRight)
            }
          }
        }
      }
      case Leaf => (Leaf, Leaf) // Found a leaf below. We were at level 0. Returning (Leaf, Leaf) will give Leaf as the lowest inserted node
    }

    def increaseHeight(t: Node, newHeight: Int): Node = t match {
      case SkipNode(value, down, right, height) => if (height >= newHeight) {t} else {increaseHeight(SkipNode(value, t, Leaf, height+1), newHeight)}
      case Leaf => Leaf
    }
    SkipList(insert_(increaseHeight(sl.head, newHeight), k, newHeight)._1, max(sl.max_height, height)) 
  }

  def remove(sl: SkipList, k: Int): SkipList = {
    def remove_(t: Node, k: Int): Node = t match {
      case SkipNode(value, down, right, height) => {
        right match {
          case SkipNode(valueR, downR, rightR, heightR) => {
            if (valueR == k) {SkipNode(value, remove_(down, k), rightR, height)}
            else if (valueR < k) {SkipNode(value, down, remove_(right, k), height)}
            else {SkipNode(value, remove_(down, k), right, height)}
          }
          case Leaf => SkipNode(value, remove_(down, k), right, height)
        }
      }
      case Leaf => t // Should happen once
    }
    SkipList(remove_(sl.head, k), sl.max_height)
  }

}

object HelloWorld {
  def main(args: Array[String]): Unit = {
    println("Hello, world!")
  }
}