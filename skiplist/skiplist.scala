import stainless.lang._

object SkipList {

  sealed abstract class Tree[K,V]

  /*
  case class Leaf[T]() extends Tree[T]
  
  case class Node[T](root: T, left: Tree[T], right: Tree[T]) extends Tree[T]
  */
  
  case class SkipNode[K,V](key: K, value: V, down: Tree[K,V], right: Tree[K,V], height: int) extends Tree[K,V]

  case class Bottom[K,V]() extends Tree[K,V]
  case class Tail[K,V]() extends Tree[K,V]
  case class Head[K,V](succ: Tree[K,V]) extends Tree[K,V]

  // note: make a head object? might simplify insert

  class SkipList[K,V](head: Head[K,V], max_height: int)



  def search(sl: SkipList[K,V], target: K): Optional[V] = {

    def search_(t: Tree[K,V], target: K): Optional[V] =  t match {
      case SkipNode(k,v,d,r,_) =>
          // found
          if(k  == target){ 
            Some(v) 
          }
          else {
            r match {
              case SkipNode(k2,_,_,_,_) => 
                // go right
                if(k2 < target) {
                  search_(r, target)
                }
                // go down
                else {
                  search_(d, target)
                }
              // might be lower
              case Tail => search_(d, target)
            }
          }
      case Bottom() => None //key not in list
    }

    search_(sl.head.succ, target)

  }

  def insert(sl: SkipList[K,V], k: K, v: V, height: int): SkipList[K,V] = {

    // operating on level l
    def level_insert(t: Tree[K,V], target: K, value: V, target_height:int): Tree[K,V] = t match {
      
      case SkipNode(k,v,down,right,current_level) =>
        right match {
          case SkipNode(k1,_,_,_,_) =>
            if(k1 < target){
              level_insert(right, target, value, l)
            }
            else{ // t is pred of target at level l
              if(current_level > height) {
                level_insert(down, target, value, target_height)
              }
              if(h=0) TODO stitch(pred, left, right)
              else (h>0)
                val new_down = level_insert(down, target, value, target_height)
                SkipNode(k, v, new_down, right, current_level)
              }
              
            }
          case Tail => TODO
        }

    }

    def  insert(t: Tree[K,V], k: K, v: V, height: int): Tree[K,V] = {

      // if new level, raise first element to this new level
      if(height > t.height) {
        val higher_t = SkipNode(t.k, t.v, t, Tail(), t.height+1)
        insert(higher_t, k, v, t.height + 1 )
      }
      else {
        val level_pred =  
      }

    

    }

    val first_value = sl.h.succ.k
    if( first_value > k) {
    
    }
    else {
      insert(sl.t, k, v, height)
    } 

  }

    





  }

  def remove() = {}

}