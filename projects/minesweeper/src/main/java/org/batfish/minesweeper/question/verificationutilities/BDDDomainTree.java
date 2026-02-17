package org.batfish.minesweeper.question.verificationutilities;

import net.sf.javabdd.BDD;
import org.batfish.minesweeper.bdd.BDDDomain;
import org.batfish.minesweeper.bdd.TransferBDD;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;

/// Class not used - designed to help easily translate byte[] assignments to the AS
/// path/corresponding BDDDomain assignment
public record BDDDomainTree<T, D>(BDDDomainTreeNode<T> root) {
  private static <T, D> BDDDomainTree<T, D> updateUniqueValues(
      BDDDomainTree<T, D> tree, BDDDomain<D> domain, Map<T, Set<D>> valuesToDomain) {
    valuesToDomain.forEach(
        (rgx, ints) -> {
          Optional<D> value = ints.stream().findFirst();
          if (value.isPresent() && ints.size() == 1) {
            BDD bdd = domain.value(value.get());
            BDD.AllSatIterator iterator = bdd.allsat();
            assert iterator.hasNext();
            byte[] assignment = iterator.next();
            assert !iterator.hasNext();
            BDDDomainTreeNode<T> prev = tree.root;
            while (!prev.isLeaf()) {
              prev.addPossibleRegex(rgx);
              prev = assignment[prev.bddVariable] == 0 ? prev.takeZeroPath() : prev.takeOnePath();
            }
            prev.addPossibleRegex(rgx);
          }
        });
    // at the root, the assumption is no variables are given so this variable doesn't play a
    // role/no value
    tree.root.possibleValues.clear();
    return tree;
  }

  public static <T, D> BDDDomainTree<T, D> build(
      TransferBDD tbdd, BDDDomain<D> domain, Map<T, Set<D>> valuesToDomain) {
    int depth = domain.getInteger().size();
    if (depth == 0) {
      return new BDDDomainTree<T, D>(null);
    }
    int first = domain.getInteger().support().var();
    BDDDomainTreeNode<T> root = new BDDDomainTreeNode<T>(first);
    Queue<BDDDomainTreeNode<T>> toExpand = new LinkedList<>();
    toExpand.add(root);
    while (!toExpand.isEmpty()) {
      BDDDomainTreeNode<T> recent = toExpand.remove();
      if (recent.bddVariable < first + depth) {
        int nextVar = recent.bddVariable + 1;
        if (nextVar < first + depth) {
          // next node corresponds to a variable which has an assignment
          toExpand.add(recent.addZeroPath(new BDDDomainTreeNode<T>(nextVar)));
          toExpand.add(recent.addOnePath(new BDDDomainTreeNode<T>(nextVar)));
        } else {
          // should be adding a leaf
          recent.addZeroPath(new BDDDomainTreeNode<T>(null));
          recent.addOnePath(new BDDDomainTreeNode<T>(null));
        }
      }
    }
    return updateUniqueValues(new BDDDomainTree<T, D>(root), domain, valuesToDomain);
  }

  public Set<T> valuesFromByteAssignment(byte[] assignment) {
    // TODO better support for when byte[] doesn't mention the BDDDomain var (ie all -1)
    BDDDomainTreeNode<T> curr = this.root;
    if (curr == null) {
      return Set.of();
    }
    while (!curr.isLeaf()) {
      if (assignment[curr.bddVariable] == -1) {
        return curr.getPossibleValues();
      } else {
        assert assignment[curr.bddVariable] == 0 || assignment[curr.bddVariable] == 1;
        curr = assignment[curr.bddVariable] == 0 ? curr.takeZeroPath() : curr.takeOnePath();
      }
    }
    assert curr.possibleValues.size() <= 1;
    return curr.getPossibleValues();
  }

  public static class BDDDomainTreeNode<T> {
    private final Integer bddVariable;
    private final Set<T> possibleValues = new HashSet<>();
    private BDDDomainTreeNode<T> setToZero;
    private BDDDomainTreeNode<T> setToOne;

    public BDDDomainTreeNode(Integer bddVariable) {
      this.bddVariable = bddVariable;
      this.setToZero = null;
      this.setToOne = null;
    }

    public boolean isLeaf() {
      return this.bddVariable == null;
    }

    public BDDDomainTreeNode<T> addZeroPath(BDDDomainTreeNode<T> left) {
      this.setToZero = left;
      return this.setToZero;
    }

    public BDDDomainTreeNode<T> addOnePath(BDDDomainTreeNode<T> right) {
      this.setToOne = right;
      return this.setToOne;
    }

    public BDDDomainTreeNode<T> takeZeroPath() {
      return this.setToZero;
    }

    public BDDDomainTreeNode<T> takeOnePath() {
      return this.setToOne;
    }

    public void addPossibleRegex(T val) {
      this.possibleValues.add(val);
    }

    public Set<T> getPossibleValues() {
      return new HashSet<>(this.possibleValues);
    }
  }
}
