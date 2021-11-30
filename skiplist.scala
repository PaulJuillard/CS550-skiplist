//import stainless.lang._
import math.max
import math.min

object SkipList {
  
  
  /*
  case class Leaf[T]() extends Tree[T]
  
  case class Node[T](root: T, left: Tree[T], right: Tree[T]) extends Tree[T]
  */
  
  case class SkipList(head: Tree[BigInt,BigInt], max_height: Int)
  sealed abstract class Tree[K,V]
  case class SkipNode[K,V](key: K, value: V, down: Tree[K,V], right: Tree[K,V], height: Int) extends Tree[K,V]

  case class Bottom[K,V]() extends Tree[K,V]
  case class Tail[K,V]() extends Tree[K,V]

  // note: make a head object? might simplify insert

  // TODO : Reread code (Hugo au moins)
  // TODO : Make sure first element is always +inf, and last element is always +inf (or make Stainless assume, TBD later)
  // TODO : Add randomness with insert
  // TODO : Test
  // TODO : Write invariants and make Stainless prove them
  // Invariants : If insert element then search, found
  // If search element in the list, it is found
  // If remove then search, not found
  // Every level is a subset of the level below
  // Search is probabilistically log




  def search(sl: SkipList, target: BigInt): Option[BigInt] = {
    def search_bis(t: Tree[BigInt,BigInt], target: BigInt): Option[BigInt] = t match {
      case SkipNode(k,v,d,r,_) =>
          // found
          if(k  == target) { 
            Some(v) 
          }
          else {
            r match {
              case SkipNode(k2,_,_,_,_) => 
                // go right
                if(k2 < target) {
                  search_bis(r, target)
                }
                // go down
                else {
                  search_bis(d, target)
                }
              // might be lower
              case Tail() => search_bis(d, target)
              case Bottom() => None
            }
          }
      case Bottom() => None //key not in list
      case Tail() => None
    }

    val a = sl.head
    search_bis(a, target)

  }

  def insert(sl: SkipList, k: BigInt, v: BigInt, height: Int): SkipList = {


    def search_right(t: Tree[BigInt,BigInt], target: BigInt): Tree[BigInt,BigInt] = t match {
      case SkipNode(k,v,down,right,current_level) =>
        if (k == target){t}
        else search_right(right,target)
      case Tail() => t
      case Bottom() => t
    }
    // operating on level l
    def level_insert(t: Tree[BigInt,BigInt], target: BigInt, value: BigInt, target_height:Int): Tree[BigInt,BigInt] = t match {
      
      case SkipNode(k,v,down,right,current_level) => {
        right match {
          case Tail() => {        
            if(current_level > height) {
              level_insert(down, target, value, target_height)
            }
            if(current_level == 0){
              val newNode = SkipNode(target, value, Bottom(), right, current_level)
              SkipNode(k,v,down,newNode,current_level)
            }
            else {
              val new_down = level_insert(down, target, value, target_height)

              val lower_new_node = search_right(new_down,target)
              val newNode = SkipNode(target, value, lower_new_node, right, current_level)

              SkipNode(k, v, new_down, right, current_level)
            }
          }
          case SkipNode(k2,_,_,_,_) => {
            if(k2<target){
              level_insert(right, target, value, target_height)
            }
            else{ // t is pred of target at level l
              if(current_level > height) {
                level_insert(down, target, value, target_height)
              }
              if(current_level == 0){
                val newNode = SkipNode(target, value, Bottom(), right, current_level)
                SkipNode(k,v,down,newNode,current_level)
              }
              else{
                val new_down = level_insert(down, target, value, target_height)

                val lower_new_node = search_right(new_down,target)
                val newNode = SkipNode(target, value, lower_new_node, right, current_level)

                SkipNode(k, v, new_down, right, current_level)

              }
          }
        }
        case Bottom() => t
        
          
        }
      }
      case Tail() => t
      case Bottom() => t
    }

    // If the key to insert is smaller than the current smallest key
    def insert_first(t: Tree[BigInt,BigInt], k: BigInt, v: BigInt, height: Int): Tree[BigInt,BigInt] =  t match{
      case SkipNode(_,_,_,_,h) => {
        if(h == 0){
          SkipNode(k, v, Bottom(), t, 0)
        } else {
          val lower_first = insert_first(t, k, v, height)
          SkipNode(k, v, Bottom(), t, h)
        }
      }
      case _ => t
    }
    
    def insert(t: Tree[BigInt,BigInt], k: BigInt, v: BigInt, height: Int): Tree[BigInt,BigInt] = t match {
      
      // if new level, raise first element to this new level
      case SkipNode(k2,v2,_,_,h) => {
        
        if( k < k2){
          val new_tree = insert_first(t,k,v,h)
          if(height > h) {
            SkipNode(k, v, new_tree, Tail(), h+1)
          }else {
            new_tree
          }
          
        }
        if(height > h) {
          val higher_t = SkipNode(k2, v2, t, Tail(), h+1)
          insert(higher_t, k, v, h + 1)
        }
        level_insert(t, k, v, height)
      }
      case _ => t
    }
    val new_tree = insert(sl.head, k, v, height)
    val new_height = max(min(height,sl.max_height+1),sl.max_height)
    new SkipList(new_tree,new_height) //TODO:+1 ?
  }

  def remove(sl: SkipList, k: BigInt): SkipList = {
    def remove_(t: Tree[BigInt, BigInt], k: BigInt): Tree[BigInt, BigInt] = t match {
      case SkipNode(key, value, down, right, height) => {
        right match {
          case SkipNode(keyR, valueR, downR, rightR, heightR) => {
            if (keyR == k) {SkipNode(key, value, remove_(down, k), rightR, height)}
            else if (keyR < k) {SkipNode(key, value, down, remove_(right, k), height)}
            else {SkipNode(key, value, remove_(down, k), right, height)}
          }
          case Bottom() => t // Cannot happen
          case Tail() => SkipNode(key, value, remove_(down, k), right, height)
        }
      }
      case Tail() => t // Should not happen
      case Bottom() => t // Should happen once
    }
    SkipList(remove_(sl.head, k), sl.max_height)
  }

}

object HelloWorld {
  def main(args: Array[String]): Unit = {
    println("Hello, world!")
  }
}