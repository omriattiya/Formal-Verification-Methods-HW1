package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

import java.io.InputStream;
import java.util.*;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        return new TransitionSystemImpl<>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1) return false;
        for (S s : ts.getStates()) {
            Set<A> actions = new HashSet<>();
            for (Transition<S, A> t : ts.getTransitions())
                if (t.getFrom().equals(s)) {
                    if (actions.contains(t.getAction()))
                        return false;
                    actions.add(t.getAction());
                }
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1) return false;

        for (S s : ts.getStates()) {
            List<S> toStates = new ArrayList<>();

            // after this 'for' we have all the 'to states' of 's'
            for (Transition<S, A> t : ts.getTransitions())
                if (t.getFrom().equals(s))
                    toStates.add(t.getTo());

            // here we are matching each 'toState`s' AP with one another to see if there are 2 with the same ap
            for (int i = 0; i < toStates.size() - 1; i++) {
                Set<P> ap = ts.getLabel(toStates.get(i));
                for (int j = i + 1; j < toStates.size(); j++) {
                    Set<P> ap2 = ts.getLabel(toStates.get(j));
                    for (P p : ap2) {
                        if (ap.contains(p))
                            return false;
                    }
                }
            }
        }
        return true;
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S, A> next;

        if (!ts.getInitialStates().contains(e.head())) {
            return false;
        }

        next = compareASandTS(ts, e);

        if (next == null) {
            return false;
        }
        return post(ts, next.head()).size() == 0;
    }


    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S, A> next;
        next = compareASandTS(ts, e);
        return next != null;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S, A> next;

        if (!ts.getInitialStates().contains(e.head())) {
            return false;
        }

        next = compareASandTS(ts, e);
        return next != null;
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S, A> next;

        next = compareASandTS(ts, e);

        if (next == null) {
            return false;
        }
        return post(ts, next.head()).size() == 0;
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        for (Transition<S, A> transition : ts.getTransitions())
            if (transition.getFrom().equals(s))
                return false;
        return true;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> post_states = new HashSet<>();
        for (Transition<S, ?> transition : ts.getTransitions()) {
            if (transition.getFrom().equals(s))
                post_states.add(transition.getTo());
        }
        return post_states;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> post_states = new HashSet<>();
        for (S state : c) {
            post_states.addAll(post(ts, state));
        }
        return post_states;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> post_states = new HashSet<>();
        for (Transition<S, A> transition : ts.getTransitions()) {
            if (transition.getFrom().equals(s) && transition.getAction().equals(a))
                post_states.add(transition.getTo());
        }
        return post_states;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> post_states = new HashSet<>();
        for (S state : c) {
            post_states.addAll(post(ts, state, a));
        }
        return post_states;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> pre_states = new HashSet<>();
        for (Transition<S, ?> transition : ts.getTransitions()) {
            if (transition.getTo().equals(s))
                pre_states.add(transition.getFrom());
        }
        return pre_states;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> pre_states = new HashSet<>();
        for (S state : c) {
            pre_states.addAll(pre(ts, state));
        }
        return pre_states;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> pre_states = new HashSet<>();
        for (Transition<S, ?> transition : ts.getTransitions()) {
            if (transition.getTo().equals(s) && transition.getAction().equals(a))
                pre_states.add(transition.getFrom());
        }
        return pre_states;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> pre_states = new HashSet<>();
        for (S state : c) {
            pre_states.addAll(pre(ts, state, a));
        }
        return pre_states;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> reachableStates = new HashSet<>();
        Set<S> currentlyDiscovering = new HashSet<>();
        Stack<S> workStack = new Stack<>();

        for (S state : ts.getInitialStates()) {
            workStack.push(state);
            currentlyDiscovering.add(state);
            while (!workStack.empty()) {
                S currState = workStack.pop();
                reachableStates.add(currState);
                currentlyDiscovering.remove(currState);
                Set<S> nextStates = post(ts, currState);
                for (S nextState : nextStates) {
                    if (currentlyDiscovering.contains(nextState)) {
                        continue;
                    }
                    workStack.push(nextState);
                }
            }
        }

        return reachableStates;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {

        TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem = interleave_all_init_except_transition_and_name(ts1, ts2);

        // init transitions
        Set<A> emptyHandShakeActionsSet = new HashSet<>();
        interleave_initTransitionFunction_handShakingActions(ts1, ts2, interleaveTransitionSystem, emptyHandShakeActionsSet);

        // init name
        interleaveTransitionSystem.setName(ts1.getName() + " ||| " + ts2.getName());

        return interleaveTransitionSystem;
    }


    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave
            (TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem = interleave_all_init_except_transition_and_name(ts1, ts2);

        // init transitions
        interleave_initTransitionFunction_handShakingActions(ts1, ts2, interleaveTransitionSystem, handShakingActions);

        // init name
        interleaveTransitionSystem.setName(ts1.getName() + " |||h " + ts2.getName());

        return interleaveTransitionSystem;
    }


    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createProgramGraph
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave
            (ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit
            (Circuit c) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph
            (ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem
            (ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product
            (TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    //****************** IMPLEMENT UNTIL HERE FOR HW1 ***************************************


    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty
            (TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }


    /***
     *      _    _      _                   ______                _   _
     *     | |  | |    | |                 |  ____|              | | (_)
     *     | |__| | ___| |_ __   ___ _ __  | |__ _   _ _ __   ___| |_ _  ___  _ __  ___
     *     |  __  |/ _ \ | '_ \ / _ \ '__| |  __| | | | '_ \ / __| __| |/ _ \| '_ \/ __|
     *     | |  | |  __/ | |_) |  __/ |    | |  | |_| | | | | (__| |_| | (_) | | | \__ \
     *     |_|  |_|\___|_| .__/ \___|_|    |_|   \__,_|_| |_|\___|\__|_|\___/|_| |_|___/
     *                   | |
     *                   |_|
     */

    private <S1, S2, A, P> void interleave_initTransitionFunction_handShakingActions(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem, Set<A> handShakingActions) {

        //transition if action in handshake and (s1,s2)-a->(s1',s2) && (s1,s2)-a->(s1,s2')
        for (A action : interleaveTransitionSystem.getActions())
            if (handShakingActions.contains(action))
                for (Transition<S1, A> transition1 : ts1.getTransitions())
                    if (transition1.getAction().equals(action))
                        for (Transition<S2, A> transition2 : ts2.getTransitions())
                            if (transition2.getAction().equals(action)) {
                                Pair<S1, S2> pairFrom = new Pair<>(transition1.getFrom(), transition2.getFrom());
                                Pair<S1, S2> pairTo = new Pair<>(transition1.getTo(), transition2.getTo());
                                interleaveTransitionSystem.addTransition(new Transition<>(pairFrom, action, pairTo));
                            }

        //transition (s1,s2)->(s1',s2)
        for (Transition<S1, A> transition : ts1.getTransitions()) {
            if (!handShakingActions.contains(transition.getAction()))
                for (S2 s2_state : ts2.getStates()) {
                    Pair<S1, S2> pairFrom = new Pair<>(transition.getFrom(), s2_state);
                    Pair<S1, S2> pairTo = new Pair<>(transition.getTo(), s2_state);
                    A action = transition.getAction();
                    interleaveTransitionSystem.addTransition(new Transition<>(pairFrom, action, pairTo));
                }
        }
        //transition (s1,s2)->(s1,s2')
        for (Transition<S2, A> transition : ts2.getTransitions()) {
            if (!handShakingActions.contains(transition.getAction()))
                for (S1 s1_state : ts1.getStates()) {
                    Pair<S1, S2> pairFrom = new Pair<>(s1_state, transition.getFrom());
                    Pair<S1, S2> pairTo = new Pair<>(s1_state, transition.getTo());
                    A action = transition.getAction();
                    interleaveTransitionSystem.addTransition(new Transition<>(pairFrom, action, pairTo));
                }
        }
    }

    private <S1, S2, A, P> void interleave_initLabels
            (TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem) {
        for (Pair<S1, S2> state : interleaveTransitionSystem.getStates()) {
            for (P proposition : ts1.getLabelingFunction().get(state.first))
                interleaveTransitionSystem.addToLabel(state, proposition);
            for (P proposition : ts2.getLabelingFunction().get(state.second))
                interleaveTransitionSystem.addToLabel(state, proposition);
        }
    }

    private <S1, S2, A, P> void interleave_initAtomicProposition
            (TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem, Set<P> atomicPropositions) {
        for (P proposition : atomicPropositions)
            interleaveTransitionSystem.addAtomicProposition(proposition);
    }

    private <S1, S2, A, P> void interleave_initActions
            (TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem, Set<A> actions) {
        for (A action : actions)
            interleaveTransitionSystem.addAction(action);
    }

    private <S1, S2, A, P> void interleave_initStates
            (TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem, Set<S1> states, Set<S2> states2) {
        Set<Pair<S1, S2>> interleaveStates = s1_x_s2(states, states2);
        for (Pair<S1, S2> s : interleaveStates)
            interleaveTransitionSystem.addState(s);
    }

    // returns a set of pairs that consists of S1xS2
    private <S1, S2> Set<Pair<S1, S2>> s1_x_s2(Set<S1> s1, Set<S2> s2) {
        Set<Pair<S1, S2>> new_set = new HashSet<>();
        for (S1 s1_item : s1) {
            for (S2 s2_item : s2) {
                new_set.add(new Pair<>(s1_item, s2_item));
            }
        }
        return new_set;
    }

    private <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave_all_init_except_transition_and_name
            (TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        // new transition system (S1 x S2, act1 U act2, ->, I1 x I2, AP1 U AP2, L)
        TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem = createTransitionSystem();

        // init states
        interleave_initStates(interleaveTransitionSystem, ts1.getStates(), ts2.getStates());

        // init initials
        interleave_initStates(interleaveTransitionSystem, ts1.getInitialStates(), ts2.getInitialStates());

        // init actions
        interleave_initActions(interleaveTransitionSystem, ts1.getActions());
        interleave_initActions(interleaveTransitionSystem, ts2.getActions());

        // init atomic proposition
        interleave_initAtomicProposition(interleaveTransitionSystem, ts1.getAtomicPropositions());
        interleave_initAtomicProposition(interleaveTransitionSystem, ts2.getAtomicPropositions());

        // init labels
        interleave_initLabels(ts1, ts2, interleaveTransitionSystem);
        return interleaveTransitionSystem;
    }

    private <S, A, P> AlternatingSequence<S, A> compareASandTS(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> next) {
        S stateFrom;
        A action;
        S stateTo;

        while (next.tail() != null) {
            stateFrom = next.head();
            action = next.tail().head();
            stateTo = next.tail().tail().head();

            if (!ts.getTransitions().contains(new Transition<>(stateFrom, action, stateTo))) { //TODO: not sure if contains will perform deep compare
                return null;
            }
            next = next.tail().tail();
        }

        return next;
    }


}
