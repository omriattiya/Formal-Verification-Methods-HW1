package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
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
        if (states.contains(aState))
            if (isInitial)
                if (!initials.contains(aState))
                    initials.add(aState);
                else if (initials.contains(aState))
                    initials.remove(aState);
                else throw new StateNotFoundException(aState);
    }

    @Override
    public void addState(STATE state) {
        states.add(state);
        labelsMap.put(state, new HashSet<>());
    }

    @Override
    public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
        if (!states.contains(t.getFrom()))
            throw new FVMException("Transition from state doesnt exist");
        if (!states.contains(t.getTo()))
            throw new FVMException("Transition to state doesnt exist");
        if (!actions.contains(t.getAction()))
            throw new FVMException("Transition action doesnt exist");
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
            throw new FVMException("state does not exist");
        if (!atomic_propositions.contains(l))
            throw new FVMException("tag does not exist");
        labelsMap.get(s).add(l);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
        if (labelsMap.containsKey(s))
            return labelsMap.get(s);
        else return new HashSet<>();
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
            throw new FVMException("action does not exist");
        for (Transition<STATE, ACTION> t : transitions) {
            if (t.getAction().equals(action))
                removeTransition(t);
        }
        actions.remove(action);
    }

    @Override
    public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
        if (atomic_propositions.contains(p))
            throw new FVMException("atomic proposition does not exist");
        for (STATE s : states)
            removeLabel(s, p);
        atomic_propositions.remove(p);
    }

    @Override
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        labelsMap.get(s).remove(l);
    }

    @Override
    public void removeState(STATE state) throws FVMException {
        if (!states.contains(state))
            throw new FVMException("state does not exist");
        for (Transition<STATE, ACTION> t : transitions) {
            if(t.getFrom().equals(state) || t.getTo().equals(state))
                removeTransition(t);
        }
        labelsMap.remove(state);
        initials.remove(state);
        states.remove(state);

    }

    @Override
    public void removeTransition(Transition<STATE, ACTION> t) {
        transitions.remove(t);
    }
}
