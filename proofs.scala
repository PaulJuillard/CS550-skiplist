package users
import users.skiplist._
import users.utils._
import users.properties._
import users.axioms._

import stainless.math.{max, min, wrapping}
import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

package object proofs {
  // Lemmas concluding that something is subset of something else
  def lem_insertRightReturnsSuperset(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueSmallerThan(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        r match {
          case r@SkipNode(valueR, downR, rightR, heightR) => {
            if (valueR <= k) {
              if (valueR == k) {
                lem_isSubsetOfItself(n, r)
              }
              else {
                sizeDecreasesToTheRight(n)
                lem_insertRightReturnsSuperset(r, k)
                lem_insertRightReturnsSkipList(n, k)
                lem_rightIsSubsetOfOtherRightImpliesSubset(n, insertedRight)
                check(isSubsetOf(n, insertedRight))
              }
            }
            else {
              val nD = findNewDown(d, k)
              val nR = SkipNode(k, nD, r, h)
              lem_insertRightReturnsSkipList(n, k)
              lem_toTheRightIsStrictSubset(r, nR)
              lem_rightIsSubsetOfOtherRightImpliesSubset(n, insertedRight)
              check(isSubsetOf(n, insertedRight))
            }
          }
          case Leaf => ()
        }
      }
    }
    isSubsetOf(n, insertRight(n, k))
  }.holds

  def lem_rightIsSubsetOfOtherRightImpliesSubset(n: Node, lower: Node): Boolean = {
    require(n.isSkipNode)
    require(n.isSkipList)
    require(lower.isSkipList)
    require(lower.isSkipNode)
    require(rightIsSkipNode(n))
    require(rightIsSkipNode(lower))
    require(hasSameValue(n, lower))
    require(rightIsSubsetOfOtherRight(n, lower))
    (n, lower) match {
      case (n@SkipNode(value, down, right, _), lower@SkipNode(valueL, downL, rightL, _)) => {
        (right, rightL) match {
          case (right@SkipNode(v1, _, rightRA, _), rightL@SkipNode(v2, _, _, _)) => {
            if (lowerLevelIsStrictSuperset(right, rightL)) {
              lem_toTheRightIsStrictSubset(rightL, lower)
              lem_isStrictSupersetTransitivity(right, rightL, lower)
            }
            else if (lowerLevelIsStrictSuperset(rightRA, rightL) && v1 == v2) {
              lem_toTheRightIsStrictSubset(rightL, lower)
              lem_isStrictSupersetTransitivity(rightRA, rightL, lower)
            }
          }
        }
      }
    }
    isSubsetOf(n, lower)
  }.holds

  def lem_isSubsetOfItself(n: Node, right: Node): Boolean = {
    require(n.isSkipNode)
    require(right.isSkipNode)
    require(n.isSkipList)
    require(isRightOf(right, n))
    n match {
      case SkipNode(_, _, right, _) => {
        lem_toTheRightIsStrictSubset(right, n)
      }
    }
    isSubsetOf(n, n)
  }.holds

  def lem_insertRightZeroHeightReturnsSuperset(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueSmallerThan(k))
    require(n.hasHeight(0))
    require(n.isSkipNode)
    decreases(size(n))
    n match {
      case n@SkipNode(value, _, right, _) => {
      val insertedRight = insertRightZeroHeight(n, k)
        if (value != k) {
          right match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR < k) {
                sizeDecreasesToTheRight(n)
                lem_insertRightZeroHeightReturnsSuperset(r, k)
                lem_insertRightZeroHeightIsSkipList(n, k)
                lem_rightIsSubsetOfOtherRightImpliesSubset(n, insertedRight)
              }
              else if (valueR == k) {
                lem_isSubsetOfItself(n, r)
              }
              else if (valueR > k) {
                val nR = SkipNode(k, Leaf, n.right, n.height)
                lem_insertRightZeroHeightIsSkipList(n, k)
                lem_toTheRightIsStrictSubset(r, nR)
                lem_rightIsSubsetOfOtherRightImpliesSubset(n, insertedRight)
              }
            }
            case Leaf => ()
          }
        }
        isSubsetOf(n, insertedRight)
      }
    }
  }.holds

  def lem_isDownOfImpliesSubset(down: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    require(down.isSkipNode)
    require(n.isSkipList)
    require(isDownOf(down, n))
    decreases(size(n))
    (n, down) match {
      case (n@SkipNode(value, _, right, _), SkipNode(valueL, _, _, _)) => {
        check(value == valueL)
        right match {
          case right@SkipNode(valueR, downR, _, _) => {
            sizeDecreasesToTheRight(n)
            lem_isDownOfImpliesSubset(downR, right)
            lem_isInRightSubtreeImpliesSubset(downR, down)
            lem_isSubsetOfTransitivity(right, downR, down)
          }
          case Leaf => ()
        }
      }
    }
    isSubsetOf(n, down)
  }.holds

  def lem_isInRightSubtreeImpliesSubset(right: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    require(right.isSkipNode)
    require(n.isSkipList)
    require(isInRightSubtree(right, n))
    (n, right) match {
      case (n@SkipNode(value, _, r, _), right@SkipNode(_, _, _, _)) => {
        if (right != r) {
          lem_isInRightSubtreeImpliesSubset(right, r)
          lem_toTheRightIsSubset(r, n)
          lem_isInRightSubtreeImpliesSkipList(right, n)
          lem_isSubsetOfTransitivity(right, r, n)
        }
        else {
          lem_toTheRightIsSubset(r, n)
        }
      }
    }
    isSubsetOf(right, n)
  }.holds

  def lem_toTheRightIsSubset(right: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    require(right.isSkipNode)
    require(n.isSkipList)
    require(isRightOf(right, n))
    (n, right) match {
      case (SkipNode(_, _, _, _), right@SkipNode(valueR, _, rightR, _)) => {
        lem_toTheRightIsStrictSubset(right, n)
      }
    }
    isSubsetOf(right, n)
  }.holds

  def lem_toTheRightIsStrictSubset(right: Node, n: Node): Boolean = {
    require(n.isSkipNode)
    require(right.isSkipNode)
    require(n.isSkipList)
    require(isInRightSubtree(right, n))
    (n, right) match {
      case (n@SkipNode(_, _, _, _), right@SkipNode(valueR, _, rightR, _)) => {
        lem_isInRightSubtreeImpliesValueIsAlsoIn(n, right, valueR)
        rightR match {
          case SkipNode(_, _, _, _) => {
            lem_rightIsAlsoInRightSubtree(n, right)
            lem_toTheRightIsStrictSubset(rightR, n)
          }
          case Leaf => ()
        }
      }
    }
    lowerLevelIsStrictSuperset(right, n)
  }.holds

  def lem_plugLowerLevelReturnsSuperset(currentLeftmost: Node, lowerLeftmost: Node): Boolean = {
    require(currentLeftmost.isSkipNode)
    require(lowerLeftmost.isSkipNode)
    require(currentLeftmost.isSkipList)
    require(lowerLeftmost.isSkipList)
    require(isSubsetOf(currentLeftmost, lowerLeftmost))
    require(nodeHeight(currentLeftmost) > 0)
    require(nodeHeight(currentLeftmost) == nodeHeight(lowerLeftmost) + 1)
    decreases(size(currentLeftmost))

    val plugged = plugLowerLevel(currentLeftmost, lowerLeftmost)
    (currentLeftmost, lowerLeftmost) match {
      case (currentLeftmost@SkipNode(value, down, right, height), lowerLeftmost@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(lowerLeftmost, value)
        right match {
          case right@SkipNode(valueR, _, _, _) => {
            lem_plugLowerLevelReturnsSkipList(currentLeftmost, lowerLeftmost)
            sizeDecreasesToTheRight(currentLeftmost)
            lem_plugLowerLevelReturnsSuperset(right, newDown)
            lem_rightIsSubsetOfOtherRightImpliesSubset(currentLeftmost, plugged)
          }
          case Leaf => () 
        }
      }
    }
    isSubsetOf(currentLeftmost, plugged)
  }.holds

  def lem_isSubsetOfTransitivity(a: Node, b: Node, c: Node): Boolean = {
    require(a.isSkipNode)
    require(b.isSkipNode)
    require(c.isSkipNode)
    require(a.isSkipList)
    require(b.isSkipList)
    require(c.isSkipList)
    require(isSubsetOf(a, b))
    require(isSubsetOf(b, c))
    
    (a,b,c) match {
      case (a@SkipNode(valueA,_,rightA,_), b@SkipNode(valueB, _,rightB,_), c@SkipNode(valueC,_,rightC,_)) => {
        if ((lowerLevelIsStrictSuperset(rightB, c) && valueB == valueC)) {
          if ((lowerLevelIsStrictSuperset(rightA, b) && valueA == valueB)) {
            rightA match {
              case SkipNode(valueRA,_,rightRA,_) => {
                lem_subsetAndRightSubtreeCombine(c, b, valueRA)
                lem_strictSupersetCarriesToTheRight(b, rightA)
                lem_isStrictSupersetTransitivity(rightRA, rightB, c)
              }
              case Leaf => ()
            }
          }
          else if (lowerLevelIsStrictSuperset(a, b)) {
            lem_subsetAndRightSubtreeCombine(c, b, valueA)
            lem_strictSupersetCarriesToTheRight(b, a)
            lem_isStrictSupersetTransitivity(rightA, rightB, c)
          }
        }
        else if (lowerLevelIsStrictSuperset(b, c)) {
          if ((lowerLevelIsStrictSuperset(rightA, b) && valueA == valueB)) {
            lem_isStrictSupersetTransitivity(rightA, b, c)
          }
          else if (lowerLevelIsStrictSuperset(a, b)) {
            lem_isStrictSupersetTransitivity(a, b, c)
          }
        }
      }
    }
    isSubsetOf(a,c)
  }.holds

  def lem_isStrictSupersetTransitivity(a: Node, b: Node, c: Node): Boolean = {
    require(b.isSkipNode)
    require(c.isSkipNode)
    require(lowerLevelIsStrictSuperset(a, b))
    require(lowerLevelIsStrictSuperset(b, c))
    (a,b,c) match {
      case (a@SkipNode(valueA,_,rightA,_), b@SkipNode(valueB, _,rightB,_), c@SkipNode(valueC,_,rightC,_)) => {
        lem_subsetContainsImpliesContains(c, b, valueA)
        lem_isStrictSupersetTransitivity(rightA, b, c)
      }
      case (Leaf, _, _) => ()
    }
    lowerLevelIsStrictSuperset(a, c)
  }.holds

  def lem_subsetContainsImpliesContains(a: Node, b: Node, v: Int): Boolean = {
    require(b.isSkipNode)
    require(a.isSkipNode)
    require(isInRightSubtree(v, b))
    require(lowerLevelIsStrictSuperset(b, a))
    b match {
      case SkipNode(value, _, right, _) => {
        right match {
          case right@SkipNode(valueR, _, _, _) => {
            if (valueR != v) {
              lem_subsetContainsImpliesContains(a, right, v)
            }
          }
        }
      }
    }
    isInRightSubtree(v, a)
  }.holds

  def lem_strictSupersetCarriesToTheRight(n: Node, right: Node): Boolean = {
    require(lowerLevelIsStrictSuperset(right, n))
    require(n.isSkipNode)
    require(right.isSkipNode)
    require(n.isSkipList)
    require(right.isSkipList)
    decreases(size(right))
    (n, right) match {
      case (SkipNode(_, _, r, _), right@SkipNode(valueR, _, rightR, _)) => {
        rightR match {
          case SkipNode(valueRA, _, rightRA, _) => {
            lem_inRightSubtreeImpliesRightValueAtMost(n, r, valueR)
            lem_toTheRightIsStrictSubset(rightR, right)
            lem_isStrictSupersetTransitivity(rightR, right, n)
            sizeDecreasesToTheRight(right)
            lem_strictSupersetCarriesToTheRight(n, rightR)
          }
          case Leaf => ()
        }
        lowerLevelIsStrictSuperset(rightR, r)
      }
    }
  }.holds

  def lem_subsetAndRightSubtreeCombine(n: Node, right: Node, v: Int): Boolean = {
    require(n.isSkipList)
    require(right.isSkipList)
    require(n.isSkipNode)
    require(isSubsetOf(right, n))
    require(isInRightSubtree(v, right))
    right match {
      case SkipNode(_, _, rightR@SkipNode(value, _, _, _) , _) => {
        if (value != v) {
          lem_subsetAndRightSubtreeCombine(n, rightR, v)
        }
      }
    }
    isInRightSubtree(v, n)
  }.holds

  // Lemmas about implications of isInRightSubtree
  def lem_isInRightSubtreeImpliesSkipList(right: Node, n: Node): Boolean = {
    require(n.isSkipList)
    require(isInRightSubtree(right, n))
    n match {
      case SkipNode(_, _, r, _) => {
        if (r != right) {
          lem_isInRightSubtreeImpliesSkipList(right, r)
        }
      }
    }
    right.isSkipList
  }.holds

  def lem_inRightSubtreeImpliesRightValueAtMost(n: Node, right: Node, v: Int): Boolean = {
    require(isInRightSubtree(v, n))
    require(right.isSkipNode)
    require(n.isSkipList)
    require(isRightOf(right, n))
    n match {
      case SkipNode(_, _, r@SkipNode(rV, _, _, _), _) => {
        if (rV != v) {
          lem_isInRightSubtreeImpliesSelfValueIsLower(r, v)
        }
      }
    }
    right.valueAtMost(v)
  }.holds

  def lem_valueAtRightIsHigher(n: SkipNode, r: SkipNode): Unit = {
    require(n.isSkipList)
    require(r.isSkipList)
    require(isInRightSubtree(r, n))
    n.right match {
      case Leaf => ()
      case rN@SkipNode(value, down, right, height) => 
        if (rN != r){
          lem_valueAtRightIsHigher(rN,r)
        }
    }
  } ensuring (_ => n.value<r.value)

  def lem_valueAtRightIsHigher(n: SkipNode, r: Int): Unit = {
    require(n.isSkipList)
    require(isInRightSubtree(r, n))
    n.right match {
      case Leaf => ()
      case rN@SkipNode(value, down, right, height) => 
        if (rN.value != r){
          lem_valueAtRightIsHigher(rN,r)
        }
    }
  } ensuring (_ => n.value<r)
  
  def lem_higherRootHasLowerValue(n: Node, lower: Node): Unit = {
    require(n.isSkipNode)
    require(lower.isSkipNode)
    require(n.isSkipList)
    require(lower.isSkipList)
    require(nodeHeight(n) > 0)
    require(nodeHeight(lower)+1 == nodeHeight(n))
    require(isSubsetOf(n,lower))
    (n, lower) match {
      case (high@SkipNode(value, down, right, _), low@SkipNode(valueL, _, _, _)) => {
        if(value!=valueL){
          down match {
            case d@SkipNode(vD, _, _, _) => {
              lem_valueAtRightIsHigher(low,vD)
            }
          }
        }
      }
    }
  } ensuring (_ => hasValueAtLeast(n, lower))
  
  def lem_skipnodeToTheRightAlsoHasKeyToTheRight(n: Node, r: Node, v: Int): Unit = {
    require(n.isSkipNode)
    require(r.valueSmallerThan(v))
    require(n.isSkipList)
    require(r.isSkipList)
    require(isInRightSubtree(r, n))
    require(isInRightSubtree(v, n))
    decreases(sizeRight(n))
    n match {
      case sN@SkipNode(value, down, right, height) => {
        right match{
          case sR@SkipNode(_, _, _, _) => {
            if (sR != r){
              r match {
                case skipR@SkipNode(_,_,_,_) => {
                  lem_valueAtRightIsHigher(sR,skipR)
                  lem_skipnodeToTheRightAlsoHasKeyToTheRight(sR,skipR,v)
                }
              }
            }
          }
        }
      }
    }
  } ensuring (_ => isInRightSubtree(v, r))

  def lem_toTheRightIsStillSuperset(newLowerLeftmost: Node, newDown: Node, n: Node, v: Int): Unit = {
    require(n.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(lowerLevelIsStrictSuperset(n, newLowerLeftmost))
    require(isInRightSubtree(newDown, newLowerLeftmost))
    require(n.hasValue(v))
    require(newDown.valueSmallerThan(v))
    decreases(size(n))
    (newDown, n) match {
      case (newDown@SkipNode(value, down, right, height), n@SkipNode(valueN, _, rightN, _)) => {
        lem_isInRightSubtreeInequality(newLowerLeftmost, newDown, valueN)
        sizeDecreasesToTheRight(n)
        rightN match {
          case rightN@SkipNode(valueR, _, _, _) =>  lem_toTheRightIsStillSuperset(newLowerLeftmost, newDown, rightN, valueR)
          case Leaf => ()
        }
      }
    }
  } ensuring (_ => isSubsetOf(n, newDown))
  
  def lem_newDownIsInRightSubtreeOfOld(n: Node, k: Int): Unit = {
    require(n.isSkipList)
    require(n.valueSmallerThan(k))
    decreases(sizeRight(n))
    (findNewDown(n, k), n) match {
      case (SkipNode(value, down, right, height), n@SkipNode(_, _, rightN, _)) => {
        rightN match {
          case SkipNode(valueR, _, _, _) => {
            if (valueR < k) {
              lem_newDownIsInRightSubtreeOfOld(rightN, k)
            }
            else if (valueR > k) {
              lem_newDownWithTooHighKeyNodeReturnsLeaf(rightN, k)
            }
          }
          case Leaf => ()
        }
      }
      case (Leaf, _) => ()
    }
  } ensuring (_ => isInRightSubtree(findNewDown(n, k), n))

  def lem_bothInRightSubtreeWithLowerValue(n: Node, a: Node, b: Node, v1: Int, v2: Int): Boolean = {
    require(n.isSkipList)
    require(a.hasValue(v1))
    require(b.hasValue(v2))
    require(v1 < v2)
    require(isInRightSubtree(a, n))
    require(isInRightSubtree(b, n))
    n match {
      case SkipNode(_, _, right, _) => {
        if (right != a) {
          lem_isInRightSubtreeImpliesValueIsAlsoIn(n, b, v2)
          lem_rightSubtreeDoesNotSkipValues(n, a, v2)
          lem_bothInRightSubtreeWithLowerValue(right, a, b, v1, v2)
        }
      }
    }
    isInRightSubtree(b, a)
  }.holds

  def lem_rightIsAlsoInRightSubtree(n: SkipNode, x: SkipNode): Unit = {
    require(isInRightSubtree(x, n))
    n.right match {
      case Leaf => ()
      case r@SkipNode(value, down, right, height) => {
        if (r != x) {
          lem_rightIsAlsoInRightSubtree(r, x)
        } 
      }
    }
  } ensuring (_ => isInRightSubtree(x.right, n))

  def lem_isInRightSubtreeTransitive(n1: SkipNode, n2: SkipNode, n3: SkipNode): Unit = {
    require(isInRightSubtree(n2, n1))
    require(isInRightSubtree(n3, n2))
    if (n3 != n2.right) {
      lem_rightIsAlsoInRightSubtree(n1, n2)
      n2.right match {
        case n2R@SkipNode(_, _, _, _) => {
          lem_isInRightSubtreeTransitive(n1, n2R, n3)
        }
      }
    }
    else {
      lem_rightIsAlsoInRightSubtree(n1, n2)
    }
  } ensuring (_ => isInRightSubtree(n3, n1))

  def lem_isInRightSubtreeTransitive(n1: SkipNode, n2: SkipNode, n3: Int): Unit = {
    require(isInRightSubtree(n2, n1))
    require(isInRightSubtree(n3, n2))
    if (n1.right != n2) {
      n1.right match {
        case r@SkipNode(_, _, _, _) => lem_isInRightSubtreeTransitive(r, n2, n3)
      }
    }
  } ensuring (isInRightSubtree(n3, n1))

  // Proof that isInRightSubtree(node, node) implies isInRightSubtree(v, node)
  def lem_isInRightSubtreeImpliesValueIsAlsoIn(n: Node, target: Node, v: Int): Unit = {
    require(n.isSkipNode)
    require(target.hasValue(v))
    require(isInRightSubtree(target, n))
    decreases(sizeRight(n))
    n match {
      case n@SkipNode(_, _, right, _) => {
        if (target != right) {
          right match {
            case r@SkipNode(_, _, _, _) => {
              lem_isInRightSubtreeImpliesValueIsAlsoIn(r, target, v)
            }
          }
        }
      }
    }
  } ensuring (_ => isInRightSubtree(v, n))

  def lem_isInRightSubtreeImpliesSelfValueIsLower(n: SkipNode, k: Int): Unit = {
    require(n.isSkipList)
    require(isInRightSubtree(k, n))
    decreases(sizeRight(n))
    n.right match {
      case right@SkipNode(value, _, _, _) => if (value != k) {
        lem_isInRightSubtreeImpliesSelfValueIsLower(right, k)
      }
    }
  } ensuring (_ => n.value < k)

  def lem_inRightSubtreeImpliesDifference(n: Node, x: Node): Boolean = {
    require(isInRightSubtree(x, n))
    lem_inRightSubtreeImpliesLowerMeasure(n, x)
    n != x
  }.holds

  def lem_isInRightSubtreeInequality(n: Node, a: Node, v: Int): Unit = { 
    require(n.isSkipList)
    require(isInRightSubtree(a, n))
    require(isInRightSubtree(v, n))
    require(a.valueSmallerThan(v))
    n match {
      case SkipNode(_, _, right, _) => {
        if (right != a) {
          right match {
            case SkipNode(value, _, _, _) => {
              lem_rightSubtreeDoesNotSkipValues(n, a, v)
              lem_isInRightSubtreeInequality(right, a, v)
            }
          }
        }
      }
    }
  } ensuring (_ => isInRightSubtree(v, a))

  def lem_inRightSubtreeHasSameHeight(n: SkipNode, x: SkipNode): Unit = {
    require(n.isSkipList)
    require(x.isSkipList)
    require(isInRightSubtree(x, n))
    n.right match {
      case r@SkipNode(_, _, _, _) => {
        if (x != r) {
          lem_inRightSubtreeHasSameHeight(r, x)
        }
      }
    }
  } ensuring (n.height == x.height)

  def lem_notInRightSubtreeImpliesNotInRightsRightSubtree(target: Int, n: SkipNode, x: SkipNode): Unit = {
    require(n.isSkipList)
    require(x.isSkipList)
    require(isInRightSubtree(x, n))
    require(!isInRightSubtree(target, n))

    n.right match {
      case r@SkipNode(_, _, _, _) => {
        if (x != r) {
          lem_notInRightSubtreeImpliesNotInRightsRightSubtree(target,r, x)
        }
      }
    }
  } ensuring (!isInRightSubtree(target, x))

  def lem_inRightSubtreeHasSameNodeHeight(n: Node, x: Node): Unit = {
    require(n.isSkipList)
    require(x.isSkipList)
    require(n.isSkipNode)
    require(x.isSkipNode)
    require(isInRightSubtree(x, n))
    (n, x) match {
      case (n@SkipNode(_, _, _, hN), x@SkipNode(_, _, _, hX)) => {
        lem_inRightSubtreeHasSameHeight(n, x)
      }
    }
  } ensuring (nodeHeight(n) == nodeHeight(x))

  def lem_rightSubtreeDoesNotSkipValues(n: Node, a: Node, v: Int): Unit = {
    require(n.isSkipList)
    require(isInRightSubtree(a, n))
    require(isInRightSubtree(v, n))
    require(a.valueSmallerThan(v))
    require(rightNodeIsNot(n, a))
    n match {
      case n@SkipNode(_, _, right, _) => (right, a) match {
        case (right@SkipNode(value, _, _, _), a@SkipNode(valueA, _, _, _)) => {
          lem_isInRightSubtreeImpliesValueIsAlsoIn(right, a, valueA)
          lem_isInRightSubtreeImpliesSelfValueIsLower(right, valueA)
        }
      }
    }
  } ensuring (_ => rightNodeHasValueLessThan(n, v))


  // Lemmas about implications of isLowerOf and isDownOf 
  def lem_isDownOf(n: Node, down1: Node, down2: Node, height: BigInt): Boolean = {
    require(n.isSkipNode)
    require(n.isSkipList)
    require(down1.hasHeight(height+1))
    require(down2.hasHeight(height))
    require(isLowerOf(down1, n))
    require(isLowerOf(down2, n))
    n match {
      case n@SkipNode(_, down, _, _) => {
        lem_isLowerOfImplyHeightAtLeast(n, down1, height+1)
        if (n == down1) {
          lem_isLowerOfAndSameHeightImplySame(down, down2, height)
        }
        else {
          lem_isDownOf(down, down1, down2, height)
        }
      }
    }
    isDownOf(down2, down1)
  }.holds

  def lem_lowerRightHasSmallerValueThanRight(of: SkipNode, down: SkipNode): Unit = {
    require(of.isSkipList)
    require(isDownOf(down, of))
    of.right match {
      case Leaf => ()
      case r@SkipNode(vR, dR, _, _) => {
        higherLevelIsSubsetofLowerOne(of,r)
        if (dR!=down.right) {
          (down.right, dR) match {
            case (downR@SkipNode(_, _, _, _), dR@SkipNode(vdR, _, _, _)) => {
              lem_isInRightSubtreeImpliesValueIsAlsoIn(downR, dR, vdR)
              lem_isInRightSubtreeImpliesSelfValueIsLower(downR, vdR)
            }
            case (Leaf, _) => ()
          }
        }
      }
    }
  } ensuring (hasValueAtLeast(of.right, down.right) || of.right.isLeaf)

  def lem_isLowerOfImplyHeightAtLeast(n: Node, lower: Node, height: BigInt): Boolean = {
    require(n.isSkipNode)
    require(n.isSkipList)
    require(lower.hasHeight(height))
    require(isLowerOf(lower, n))
    n match {
      case SkipNode(_, down, _, _) => {
        if (n != lower) {
          lem_isLowerOfImplyHeightAtLeast(down, lower, height)
        }
      }
    }
    n.heightAtLeast(height)
  }.holds

  def lem_isLowerOfAndSameHeightImplySame(n: Node, lower: Node, height: BigInt): Boolean = {
    require(n.isSkipList)
    require(lower.hasHeight(height))
    require(n.hasHeight(height))
    require(isLowerOf(lower, n))
    n match {
      case SkipNode(_, down, _, _) => {
        down match {
          case down@SkipNode(_, _, _, _) => {
            lem_isLowerOfImpliesSkiplist(n, lower)
            lem_greaterHeightImpliesNotLower(down, lower, height-1)
          }
          case Leaf => ()
        }
      }
    }
    lower == n
  }.holds

  def lem_isLowerOfImpliesSkiplist(n: Node, lower: Node): Boolean = {
    require(n.isSkipList)
    require(isLowerOf(lower, n))
    n match {
      case SkipNode(_, down, _, _) => {
        if (n != lower) {
          lem_isLowerOfImpliesSkiplist(down, lower)
        }
      }
      case Leaf => ()
    }
    lower.isSkipList
  }.holds

  def lem_greaterHeightImpliesNotLower(n: Node, lower: Node, height: BigInt): Boolean = {
    require(n.isSkipList)
    require(lower.isSkipList)
    require(lower.heightAtLeast(height+1))
    require(n.hasHeight(height))
    n match {
      case SkipNode(_, down, _, _) => {
        down match {
          case SkipNode(_, _, _, _) => {
            lem_greaterHeightImpliesNotLower(down, lower, height-1)
          }
          case Leaf => ()
        }
      }
    }
    !isLowerOf(lower, n)
  }.holds

  def lem_isLowerOfTransitivity(top: Node, mid: Node, bot: Node): Boolean = {
    require(isLowerOf(mid, top))
    require(isLowerOf(bot, mid))
    require(top.isSkipList)
    require(mid.isSkipList)
    decreases(size(top) + size(mid))
    top match {
      case top@SkipNode(_, down, _,_) =>
        if(top == mid) {
          mid match {
            case mid@SkipNode(_, down2, _, _) =>
              if (mid != bot) {
                lem_sizeDecreasesDown(top)
                lem_sizeDecreasesDown(mid)
                lem_isLowerOfTransitivity(down, down2, bot)
              }
            case Leaf => ()
          }
        }
        else {
          lem_sizeDecreasesDown(top)
          lem_isLowerOfTransitivity(down, mid, bot)
        }
      case Leaf => ()
    }
    isLowerOf(bot, top)
  }.holds

  def lem_isLowerOfImpliesSameValue(lower: Node, n: Node): Boolean = {
    require(n.isSkipList)
    require(isLowerOf(lower, n))
    n match {
      case n@SkipNode(v, d, r, _) => if (n != lower) {lem_isLowerOfImpliesSameValue(lower, d)}
      case Leaf => ()
    }
    lower.isLeaf || hasSameValue(n, lower)
  }.holds


  // Lemmas about methods preserving skiplist axioms and properties
  def lem_insertRightReturnsSkipList(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v != k) {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR < k) {
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightReturnsSkipList(r, k)
              }
              else {
                lem_newDownReturnsSkipList(d, k)
                lem_insertRightPreservesLevelsAxiom(n, k)
                lem_insertRightPreservesHeightAxiom(n, k)
              }
            }
            case Leaf => {
              lem_newDownReturnsSkipList(d, k)
              lem_insertRightPreservesHeightAxiom(n, k)
              lem_insertRightPreservesLevelsAxiom(n, k)
            }
          }
        }
      }
    }
    insertRight(n, k).isSkipList
  }.holds

  def lem_insertRightPreservesLevelsAxiom(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v != k) {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR < k) {
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightPreservesLevelsAxiom(r, k)
              }
              else if (valueR > k) {
                lem_newDownReturnsSkipList(d, k)
                val nD = findNewDown(d, k)
                val nR = SkipNode(k, nD, r, h)
                if (!d.isLeaf) {
                  lem_newDownReturnsSkipNodeOfValue(d, k)
                  lem_newDownIsInRightSubtreeOfOld(d, k)
                  lem_bothInRightSubtreeWithLowerValue(d, nD, downR, k, valueR)
                }
              }
            }
            case Leaf => {
              lem_newDownReturnsSkipList(d, k)
              if (!d.isLeaf) {
                lem_newDownIsInRightSubtreeOfOld(d, k)
              }
            }
          }
        }
      }
    }
    levelsAxiom(insertedRight)
  }.holds

  def lem_insertRightPreservesHeightAxiom(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    lem_insertRightPreservesPositiveHeightAxiom(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v != k) {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR < k) {
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightPreservesHeightAxiom(r, k)
              }
              else {
                lem_newDownReturnsSkipList(d, k)
                val nD = findNewDown(d, k)
                val nR = SkipNode(k, nD, r, h)
                lem_newDownReturnsSkipNodeOfValue(d, k)
              }
            }
            case Leaf => {
              lem_newDownReturnsSkipList(d, k)
              val nD = findNewDown(d, k)
              val nR = SkipNode(k, nD, r, h)
              lem_newDownReturnsSkipNodeOfValue(d, k)
            }
          }
        }
      }
    }
    heightDecreasesDown(insertedRight)
  }.holds

  def lem_insertRightPreservesPositiveHeightAxiom(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueAtMost(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        if (v != k) {
          r match {
            case r@SkipNode(valueR, downR, rightR, heightR) => {
              if (valueR < k) {
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightPreservesPositiveHeightAxiom(r, k)
              }
              else {
                lem_newDownReturnsSkipList(d, k)
              }
            }
            case Leaf => {
              lem_newDownReturnsSkipList(d, k)
            }
          }
        }
      }
    }
    hasNonNegativeHeight(insertedRight)
  }.holds

  def lem_insertRightContainsKey(n: Node, k: Int): Boolean = {
    require(n.isSkipList)
    require(n.valueSmallerThan(k))
    require(levelBelowContainsK(n, k))
    decreases(size(n))
    val insertedRight = insertRight(n, k)
    n match {
      case n@SkipNode(v, d, r, h) => {
        r match {
          case r@SkipNode(valueR, downR, rightR, heightR) => {
            if (valueR <= k) {
              sizeDecreasesToTheRight(n)
              higherLevelIsSubsetofLowerOne(n, r)
              if (valueR != k) {
                lem_skipnodeToTheRightAlsoHasKeyToTheRight(d, r.down, k)
                val nR = insertRight(r, k)
                sizeDecreasesToTheRight(n)
                lem_insertRightContainsKey(r, k)
                (nR, insertedRight) match {
                  case (nR@SkipNode(_, _, _, _), insertedRight@SkipNode(_, _, _, _)) => {
                    lem_isInRightSubtreeTransitive(insertedRight, nR, k)
                  }
                }
              }
            }
          }
          case Leaf => ()
        }
      }
    }
    isInRightSubtree(k, insertedRight)
  }.holds

  def lem_plugLowerLevelContainsKBelow(oldCurrentLeftmost: Node, newLowerLeftmost: Node, k: Int): Boolean = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(oldCurrentLeftmost.valueSmallerThan(k))
    require(isInRightSubtree(k, newLowerLeftmost))

    val plugged = plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)
    (oldCurrentLeftmost, newLowerLeftmost) match {
      case (oldCurrentLeftmost@SkipNode(value, down, right, height), newLowerLeftmost@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(newLowerLeftmost, value)
        if (lowerLevelIsStrictSuperset(oldCurrentLeftmost, newLowerLeftmost)) {
          lem_valueStillInSubtreeAfterNewDown(newLowerLeftmost, value, k)
        }
      }
    }
    levelBelowContainsK(plugged, k)
  }.holds

  def lem_valueStillInSubtreeAfterNewDown(n: Node, target: Int, k: Int): Boolean = {
    require(isInRightSubtree(k, n))
    require(isInRightSubtree(target, n))
    require(n.isSkipList)
    require(target < k)
    
    n match {
      case SkipNode(value, _, right, _) => {
        lem_inRightSubtreeImpliesRightValueAtMost(n, right, target)
        if (value != target) {
          right match {
            case SkipNode(valueR, _, _, _) => {
              if (valueR == target) {
                check(isInRightSubtree(k, findNewDown(n, target)))
              }
              else {
                lem_valueStillInSubtreeAfterNewDown(right, target, k)
              }
            }
          }
        }
      }
    }
    isInRightSubtree(k, findNewDown(n, target))
  }.holds

  def lem_increaseHeightReturnsSkiplist(n: Node, newHeight: BigInt): Unit = {
    require(n.isSkipList)
    require(newHeight >= nodeHeight(n))
    decreases(newHeight - nodeHeight(n))

    n match {
      case n@SkipNode(value, down, right, height) => {
        if (height >= newHeight) {
          ()
        } 
        else {
          val up = SkipNode(value, n, Leaf, height+1)
          lem_increaseHeightReturnsSkiplist(up, newHeight)
          ()
        }
      }
      case Leaf => ()
    }
  } ensuring ( _ => increaseHeight(n, newHeight).isSkipList)

  def lem_increaseHeightReturnsMinValueNode(n: Node, newHeight: BigInt): Unit = {
    require(n.isSkipList)
    require(newHeight >= nodeHeight(n))
    require(n.hasValue(Int.MinValue))

    decreases(newHeight - nodeHeight(n))

    n match {
      case n@SkipNode(value, down, right, height) => {
        if (height >= newHeight) {
          ()
        } 
        else {
          val up = SkipNode(value, n, Leaf, height+1)
          lem_increaseHeightReturnsMinValueNode(up, newHeight)
          ()
        }
      }
      case Leaf => ()
    }
  } ensuring ( _ => increaseHeight(n, newHeight).hasValue(Int.MinValue))
  
  def lem_increaseHeightReturnsHigherNode(n: Node, newHeight: BigInt): Unit = {
    require(n.isSkipList)
    require(newHeight >= nodeHeight(n))
    require(n.hasValue(Int.MinValue))

    decreases(newHeight - nodeHeight(n))

    n match {
      case n@SkipNode(value, down, right, height) => {
        if (height >= newHeight) {
          ()
        } 
        else {
          val up = SkipNode(value, n, Leaf, height+1)
          lem_increaseHeightReturnsHigherNode(up, newHeight)
          ()
        }
      }
      case Leaf => ()
    }
  } ensuring ( _ => nodeHeight(increaseHeight(n, newHeight)) == newHeight)
  
  def lem_insertRightZeroHeightIsSkipList(n: SkipNode, k: Int) : Unit = {
    require(n.isSkipList)
    require(n.value <= k)
    require(nodeHeight(n) == 0)

    if (n.value != k) {
      n.right match {
        case r@SkipNode(valueR, downR, rightR, heightR) => {
          if (valueR <= k) {
            sizeDecreasesToTheRight(n)
            lem_insertRightZeroHeightIsSkipList(r, k)
          }
        }
        case Leaf => {
          val newRight = SkipNode(k, Leaf, Leaf, n.height)
          val ret = SkipNode(n.value, n.down, newRight, n.height)
          check(levelsAxiom(newRight))
          check(levelsAxiom(ret))
        }
      }
    }
  } ensuring ( _ => insertRightZeroHeight(n, k).isSkipList)

  def lem_insertRightZeroHeightContainsK(n: SkipNode, k: Int) : Unit = {
    require(n.isSkipList)
    require(n.value < k)
    require(nodeHeight(n) == 0)
    n.right match {
      case r@SkipNode(valueR, downR, rightR, heightR) => {
        if (valueR < k) {
          sizeDecreasesToTheRight(n)
          lem_insertRightZeroHeightContainsK(r, k)
        }
      }
      case Leaf => ()
    }
  } ensuring ( _ => isInRightSubtree(k,insertRightZeroHeight(n, k)))
  
  def plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Unit = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    decreases(sizeRight(oldCurrentLeftmost))
    (oldCurrentLeftmost, newLowerLeftmost) match {
      case (o@SkipNode(value, down, right, height), n@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(n, value)
        assert(plugLowerLevel(o,n).isSkipNode)
        assert(hasSameValueandHeight(plugLowerLevel(o,n),o))
        right match {
          case right@SkipNode(valueR, _, _, _) => plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(right,newDown)
          case Leaf => lem_newDownReturnsSkipList(newLowerLeftmost, value)
        }
      }
    }
  } ensuring (hasNonNegativeHeight(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)) && increasesToTheRight(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)))

  def plugLowerLevelReturnsHeightDrecreasesDown(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Unit = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    decreases(sizeRight(oldCurrentLeftmost))
    (oldCurrentLeftmost, newLowerLeftmost) match {
      case (o@SkipNode(value, down, right, height), n@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(n, value)
        assert(plugLowerLevel(o,n).isSkipNode)
        assert(hasSameValueandHeight(plugLowerLevel(o,n),o))
        right match {
          case right@SkipNode(valueR, _, _, _) => {
            plugLowerLevelReturnsHeightDrecreasesDown(right,newDown)
            plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(o,n)
          }
          case Leaf => {
            if (value != valueL){
              lem_newDownReturnsSkipList(n, value)
              lem_isInRightSubtreeImpliesSelfValueIsLower(n, value)
              lem_newDownReturnsSkipNodeOfValue(n,value)
              plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(o,n)
              assert(heightDecreasesDown(newDown))
              newDown match {
                case nD@SkipNode(ndV, ndD, ndR, ndH) => {
                  assert(ndV == value)
                  lem_newDownIsInRightSubtreeOfOld(n,value)
                  lem_inRightSubtreeHasSameNodeHeight(n, nD)
                  assert(height == heightL+1)
                  assert(ndH == heightL)
                }
              }
            }
          }
        }
      }
    }
  } ensuring (heightDecreasesDown(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)))

  def plugLowerLevelReturnsLevelsAxiom(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Unit = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    decreases(sizeRight(oldCurrentLeftmost))
    (oldCurrentLeftmost, newLowerLeftmost) match {
      case (o@SkipNode(value, down, right, height), n@SkipNode(valueL, downL, rightL, heightL)) => {
        val newDown = findNewDown(n, value)
        assert(plugLowerLevel(o,n).isSkipNode)
        assert(hasSameValueandHeight(plugLowerLevel(o,n),o))
        right match {
          case right@SkipNode(valueR, downR, _, _) => {
            plugLowerLevelReturnsLevelsAxiom(right,newDown)
            lem_newDownIsInRightSubtreeOfOld(newDown,valueR)
            assert(isInRightSubtree(findNewDown(newDown, valueR), newDown))
          }
          case Leaf => lem_newDownReturnsSkipList(newLowerLeftmost, value)
        }
      }
    }
  } ensuring (levelsAxiom(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost)))

  def lem_plugLowerLevelReturnsSkipList(oldCurrentLeftmost: Node, newLowerLeftmost: Node): Unit = {
    require(oldCurrentLeftmost.isSkipList)
    require(newLowerLeftmost.isSkipList)
    require(oldCurrentLeftmost.isSkipNode)
    require(newLowerLeftmost.isSkipNode)
    require(nodeHeight(oldCurrentLeftmost) > 0)
    require(nodeHeight(oldCurrentLeftmost) == nodeHeight(newLowerLeftmost) + 1)
    require(isSubsetOf(oldCurrentLeftmost, newLowerLeftmost))
    (oldCurrentLeftmost,newLowerLeftmost) match {
      case (o@SkipNode(vO,dO,rO,hO), n@SkipNode(vN,dN,rN,hN)) => {
        plugLowerLevel(o,n) match {
          case p@SkipNode(vP, dP, rP, hP) => {
            plugLowerLevelHasNonNegativeHeightAndIncreasesToTheRight(o,n)
            plugLowerLevelReturnsLevelsAxiom(o,n)
            plugLowerLevelReturnsHeightDrecreasesDown(o,n)
            assert(plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost).isSkipList)
          }
        }
      }
    }
  } ensuring (plugLowerLevel(oldCurrentLeftmost, newLowerLeftmost).isSkipList)

  // Lemmas about size
  def lem_sizeSkipNodeIsPositive(t: SkipNode): Unit = {
  } ensuring (_ => size(t) > 0)

  def sizeDecreasesToTheRight(n: SkipNode): Unit = {
    require(n.isSkipList)
    lem_sizeAtRightIsLower(n, n.right)
    n.right match {
      case SkipNode(_, _, _, _) => assert(size(n) > size(n.right))
      case Leaf => {
        lem_sizeSkipNodeIsPositive(n)
      }
    }
  } ensuring (_ => size(n) > size(n.right))

  def lem_sizeDecreasesDown(n: SkipNode): Unit = {
  } ensuring (_ => size(n) > size(n.down))

  def lem_sizeAtRightIsLower(n: Node, x: Node): Unit = {
    require(n.isSkipList)
    require(x.isSkipList)
    require(isInRightSubtree(x, n))
    decreases(nodeHeight(n))
    n match {
      case n@SkipNode(_, down, right, _) => x match {
        case x@SkipNode(_, downR, rightR, _) => {
          lem_inRightSubtreeImpliesLowerMeasure(n, x)
          higherLevelIsSubsetofLowerOne(n, x)
          down match {
            case (down@SkipNode(_, _, _, _)) => {
              lem_sizeAtRightIsLower(down, downR)
              lem_sizeSkipNodeIsPositive(down)
            }
            case Leaf => ()
          }
        }
        case Leaf => ()
      }
      case Leaf => ()
    }
  } ensuring (_ => n.isLeaf || size(n) > size(x))
  
  def lem_inRightSubtreeImpliesLowerMeasure(n: Node, x: Node): Boolean = {
    require(isInRightSubtree(x, n))
    decreases(sizeRight(n))
    n match {
      case n@SkipNode(value, down, right, height) => {
        if (x != right) {
          x match {
            case x@SkipNode(_, _, _, _) => {
              lem_inRightSubtreeImpliesLowerMeasure(right, x)
            }
            case Leaf => ()
          }
        }
      }
    }
    sizeRight(n) > sizeRight(x)
  }.holds
  
  
  // Lemmas about isInTheList
  def lem_isInTheListImpliesInTheListOfDown(target: Int, of: SkipNode): Unit = {
    require(isInTheList(target,of))
    require(of.isSkipList)
    require(of.down.isSkipNode)
    if(target != of.value){
      if (isInRightSubtree(target,of)){
        higherLevelIsSubsetofLowerOne(target,of)
      } else {
        assert(isInTheList(target,of.down))
      }
    }
  } ensuring(isInTheList(target,of.down))

  def lem_isInTheListOfLowerImpliesInTheList(target: Int, of: SkipNode): Unit = {
    require(of.isSkipList)
    require(isInTheList(target,of.down))
  } ensuring (isInTheList(target,of))


  def lem_isInTheListImpliesHigher(target: Int, of: SkipNode, right: SkipNode): Unit = {
    require(of.isSkipList)
    require(isInRightSubtree(right,of))
    require(isInTheList(target,of))
    require(right.valueAtMost(target))
    decreases(size(of))
    lem_isInRightSubtreeImpliesSkipList(right,of)
    of.down match {
      case Leaf => {
        higherLevelIsSubsetofLowerOne(of,right)
        lem_isInRightSubtreeImpliesValueIsAlsoIn(of,right,right.value)
        lem_isInRightSubtreeImpliesSelfValueIsLower(of,right.value)
        assert(of.right.isSkipNode)
        of.right match{
          case r@SkipNode(_,_,_,_) => 
            if(r == right){
              assert(isInTheList(target,right))
            } else {
              assert(isInRightSubtree(target,of.right))
              lem_isInRightSubtreeImpliesSelfValueIsLower(r,target)
              lem_isInTheListImpliesHigher(target,r,right)
            }
        }
      }
      case d@SkipNode(_, _, _, _) => {
        higherLevelIsSubsetofLowerOne(of,right)
        lem_inRightSubtreeHasSameHeight(of,right)
        assert(right.down.isSkipNode)
        right.down match {
          case rD@SkipNode(_, _, _, _) => {
            lem_isInTheListImpliesInTheListOfDown(target,of)
            lem_sizeDecreasesDown(of)
            lem_isInTheListImpliesHigher(target,d,rD)
          }
        }
      }
    }
  } ensuring (isInTheList(target,right))
  
  def lem_notInTheListImpliesNotInRightsList(target: Int, of: SkipNode,right: SkipNode): Unit = {
    require(of.isSkipList)
    require(isInRightSubtree(right,of))
    require(!isInTheList(target,of))
    lem_isInRightSubtreeImpliesSkipList(right,of)
    of.down match {
      case Leaf => {
        higherLevelIsSubsetofLowerOne(of,right)
        lem_isInRightSubtreeImpliesValueIsAlsoIn(of,right,right.value)
        lem_isInRightSubtreeImpliesSelfValueIsLower(of,right.value)
        lem_notInRightSubtreeImpliesNotInRightsRightSubtree(target,of,right)
      }
      case d@SkipNode(_, _, _, _) => {
        higherLevelIsSubsetofLowerOne(of,right)
        lem_inRightSubtreeHasSameHeight(of,right)
        assert(right.down.isSkipNode)
        right.down match {
          case rD@SkipNode(_, _, _, _) => {
            // lem_elementOfSkipListIsSkipList(of)
            lem_sizeDecreasesDown(of)
            lem_notInTheListImpliesNotInRightsList(target,d,rD)
            lem_notInRightSubtreeImpliesNotInRightsRightSubtree(target,of,right)
          }
        }
      }
    }
  } ensuring(!isInTheList(target,right))
  
  def lem_isInTheListLargerThanNodeImpliesInRightsList(target: Int, of: SkipNode): Unit = {
    require(isInTheList(target,of))
    require(of.isSkipList)
    require(of.right.valueAtMost(target))
    decreases(size(of)+2)
    
    assert(target != of.value)
    if (isInRightSubtree(target,of)){
      assert(isInTheList(target,of.right))
    } else {
      lem_isInTheListButNotInRightsImpliesDownIsASkipnode(target,of)
      lem_isInTheListImpliesInTheListOfDown(target,of)
      // lem_elementOfSkipListIsSkipList(of)
      of.down match {
        case d@SkipNode(value, down, right, height) => {
          lem_lowerRightHasSmallerValueThanRight(of,d)
          lem_isInTheListLargerThanNodeImpliesInRightsList(target,d)
          of.right match {
            case r@SkipNode(vR, dR, rR, hR) => {
              lem_isInTheListImpliesHigher(target,of,r)
              assert(isInTheList(target,r))
          }
            case Leaf => assert(isInTheList(target,of.right))
          }
        }
        case Leaf => assert(isInTheList(target,of.right))
      }
    }
  } ensuring(isInTheList(target,of.right))
  
  def lem_isInTheListButNotInRightsImpliesDownIsASkipnode(target: Int, of: SkipNode):Unit = {
    require(of.isSkipList)
    require(isInTheList(target,of))
    require(!isEqualOrInRightSubtree(target,of))
    
    assert(of.value != target)
    assert(!isInRightSubtree(target,of))
    assert(isInTheList(target,of.down))
    assert(!of.down.isLeaf)
  } ensuring(!of.down.isLeaf)

  def lem_isInTheListImpliesInTheListOfLowerOne(target: Int, of : SkipNode): Unit = {
    require(of.isSkipList)
    require(isInTheList(target,of))
    require(of.down.isSkipNode)
    if(isInRightSubtree(target,of)){
      higherLevelIsSubsetofLowerOne(target,of)
    }
  } ensuring(isInTheList(target,of.down))

  def lem_isInRightSubtreeImpliesValueHigher(target: Int, of: Node): Unit = {
    require(of.isSkipList)
    require(of.isSkipNode)
    require(of.valueHigherThan(target))
    decreases(sizeRight(of))
    of match {
      case of@SkipNode(value, down, r, height) => {
        r match {
          case r@SkipNode(valueR, _, rightR, _) => {
            // lem_elementOfSkipListIsSkipList(of)
            lem_valueAtRightIsHigher(of,r)
            assert(valueR>value)
            assert(valueR>target)
            lem_isInRightSubtreeImpliesValueHigher(target,r)
          }
          case Leaf => ()
        }
      }
    }
  } ensuring(!isInRightSubtree(target,of))


  // No category
  def lem_findNewDownHasGivenHeightAndValue(t: Node, v: Int): Boolean = {
    require(t.isSkipList)
    require(findNewDown(t, v).isSkipNode)
    t match {
      case SkipNode(value, down, right, height) => {
        if (value != v) {
          lem_findNewDownHasGivenHeightAndValue(right, v)
        }
      }
    }
    findNewDown(t, v).hasValue(v) && hasSameHeight(findNewDown(t, v), t)
  }.holds

  def lem_isInListIfInZero(k: Int, n: Node, levelZero: Node) : Unit = {
    require(n.isSkipList)
    require(isLowerOf(levelZero, n))
    require(levelZero.hasValue(Int.MinValue))
    require(levelZero.hasHeight(0))
    require(isInTheList(k, levelZero))
    n match {
      case SkipNode(value, down, right, height) => 
        if (height != 0)  {
          lem_isInListIfInZero(k, down, levelZero)
        }
      case Leaf => ()
    }
  } ensuring (isInTheList(k, n))

  def lem_newDownReturnsSkipList(t: Node, v: Int): Unit = {
    require(t.isSkipList)
    t match {
      case t@SkipNode(value, _, right, _) => {
        if (value != v) {
          lem_newDownReturnsSkipList(right, v)
        }
      }
      case Leaf => ()
    }
  } ensuring (_ => findNewDown(t, v).isSkipList)

  // Proof that if newDown contains k, it returns a skipnode of value k
  def lem_newDownReturnsSkipNodeOfValue(n: Node, v: Int): Unit = {
    require(n.isSkipList)
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
                  lem_isInRightSubtreeTransitive(n, r, v)
                  lem_sizeSkipNodeIsPositive(r)
                }
              }
              sizeDecreasesToTheRight(n)
              lem_newDownReturnsSkipNodeOfValue(r, v)
            }
          }
        }
      }
    }
  }.ensuring(_=> findNewDown(n, v).hasValue(v) && hasSameHeight(findNewDown(n, v), n))

  def lem_newDownWithTooHighKeyNodeReturnsLeaf(n: Node, k: Int): Unit = {
    require(n.isSkipList)
    require(n.valueHigherThan(k))
    decreases(sizeRight(n))
    n match {
      case SkipNode(_, _, right, _) => right match {
        case right@SkipNode(_, _, _, _) => {
          lem_newDownWithTooHighKeyNodeReturnsLeaf(right, k)
        }
        case Leaf => ()
      }
    }
  } ensuring (_ => findNewDown(n, k) == Leaf)
}