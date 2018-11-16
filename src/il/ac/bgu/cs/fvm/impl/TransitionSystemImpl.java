package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.*;


public class TransitionSystemImpl<STATE, ACTION, ATOMIC_PROPOSITION> implements TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> {

    private String name;
    private Set<ACTION> actions;
    private Set<STATE> initials;
    private Set<STATE> states;
    private Set<Transition<STATE, ACTION>> transitions;
    private Set<ATOMIC_PROPOSITION> atomic_propositions;
    private Map<STATE, Set<ATOMIC_PROPOSITION>> labelsMap;

    TransitionSystemImpl() {
        name = "";
        actions = new HashSet<>();
        initials = new HashSet<>();
        states = new HashSet<>();
        transitions = new HashSet<>();
        atomic_propositions = new HashSet<>();
        labelsMap = new HashMap<>();
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void addAction(ACTION anAction) {
        actions.add(anAction);
    }

    @Override
    public void setInitial(STATE aState, boolean isInitial) throws StateNotFoundException {
        if (states.contains(aState)) {
            if (isInitial) {
                if (!initials.contains(aState))
                    initials.add(aState);
            } else if (initials.contains(aState))
                initials.remove(aState);
            else
                throw new StateNotFoundException(aState);
        } else throw new StateNotFoundException(aState);
    }

    @Override
    public void addState(STATE state) {
        states.add(state);
        labelsMap.put(state, new HashSet<>());
    }

    @Override
    public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
        if (!states.contains(t.getFrom()) || !states.contains(t.getTo()) || !actions.contains(t.getAction()))
            throw new InvalidTransitionException(t);
        transitions.add(t);
    }

    @Override
    public Set<ACTION> getActions() {
        return actions;
    }

    @Override
    public void addAtomicProposition(ATOMIC_PROPOSITION p) {
        atomic_propositions.add(p);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
        return atomic_propositions;
    }

    @Override
    public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
        if (!states.contains(s))
            throw new StateNotFoundException(s);
        if (!atomic_propositions.contains(l))
            throw new InvalidLablingPairException(s, l);
        labelsMap.get(s).add(l);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
        if (!states.contains(s))
            throw new StateNotFoundException(s);
        return labelsMap.get(s);
    }

    @Override
    public Set<STATE> getInitialStates() {
        return initials;
    }

    @Override
    public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
        return labelsMap;
    }

    @Override
    public Set<STATE> getStates() {
        return states;
    }

    @Override
    public Set<Transition<STATE, ACTION>> getTransitions() {
        return transitions;
    }

    @Override
    public void removeAction(ACTION action) throws FVMException {
        if (!actions.contains(action))
            throw new DeletionOfAttachedActionException(action, TransitionSystemPart.ACTIONS);
        for (Transition<STATE, ACTION> t : transitions) {
            if (t.getAction().equals(action))
                throw new DeletionOfAttachedActionException(action, TransitionSystemPart.ACTIONS);
        }
        actions.remove(action);
    }

    @Override
    public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
        if (!atomic_propositions.contains(p))
            throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.ATOMIC_PROPOSITIONS);
        for (STATE s : states)
            if (labelsMap.get(s).contains(p))
                throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.LABELING_FUNCTION);
        atomic_propositions.remove(p);
    }

    @Override
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        if (!states.contains(s))
            throw new StateNotFoundException(s);
        if (!atomic_propositions.contains(l))
            throw new InvalidLablingPairException(s, l);
        if (!labelsMap.get(s).contains(l))
            throw new DeletionOfAttachedAtomicPropositionException(l, TransitionSystemPart.LABELING_FUNCTION);
        labelsMap.get(s).remove(l);
    }

    @Override
    public void removeState(STATE state) throws FVMException {
        if (!states.contains(state))
            throw new StateNotFoundException(state);
        if (initials.contains(state))
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.INITIAL_STATES);
        if (labelsMap.get(state).size() > 0)
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.LABELING_FUNCTION);
        for (Transition<STATE, ACTION> t : transitions) {
            if (t.getFrom().equals(state) || t.getTo().equals(state))
                throw new DeletionOfAttachedStateException(state, TransitionSystemPart.TRANSITIONS);
        }
        states.remove(state);
    }

    @Override
    public void removeTransition(Transition<STATE, ACTION> t) {
        if (!states.contains(t.getFrom()) || !states.contains(t.getTo()) || !actions.contains(t.getAction()))
            throw new InvalidTransitionException(t);
        transitions.remove(t);
    }
}
