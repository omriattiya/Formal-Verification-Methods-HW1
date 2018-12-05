package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.InterleavingActDef;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.tree.TerminalNodeImpl;

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
                    //2 states with empty ap
                    if (ap2.size() == 0 && ap.size() == 0)
                        return false;
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
        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        for (Transition<S, A> transition : ts.getTransitions())
            if (transition.getFrom().equals(s))
                return false;
        return true;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
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
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
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
                    if (currentlyDiscovering.contains(nextState) || reachableStates.contains(nextState)) {
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

        remove_unreachable(interleaveTransitionSystem);

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

        remove_unreachable(interleaveTransitionSystem);

        return interleaveTransitionSystem;
    }


    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave
            (ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> interleavedPG = new ProgramGraphImpl<>();
        interleavedPG.setName(pg1.getName() + "_interleaved_with_" + pg2.getName());


        // Adding States
        for (L1 pg1_loc : pg1.getLocations()) {
            for (L2 pg2_loc : pg2.getLocations()) {
                interleavedPG.addLocation(new Pair<>(pg1_loc, pg2_loc));
            }
        }

        // Setting Initial States
        for (Pair<L1, L2> pg_loc : interleavedPG.getLocations()) {
            if (pg1.getInitialLocations().contains(pg_loc.first) && pg2.getInitialLocations().contains(pg_loc.second)) {
                interleavedPG.setInitial(pg_loc, true);
            }
        }

        // Adding Initialization Lists
        for (List<String> pg1_initialization : pg1.getInitalizations()) {
            for (List<String> pg2_initialization : pg2.getInitalizations()) {
                List<String> all = new ArrayList<>(pg1_initialization);
                all.addAll(pg2_initialization);
                interleavedPG.addInitalization(all);
            }
        }

        // Adding Transitions From PG1
        for (PGTransition<L1, A> pg1_trans : pg1.getTransitions()) {
            for (Pair<L1, L2> pg_location1 : interleavedPG.getLocations()) {
                if (pg_location1.first.equals(pg1_trans.getFrom())) {
                    for (Pair<L1, L2> pg_location2 : interleavedPG.getLocations()) {
                        if (pg_location2.first.equals(pg1_trans.getTo()) && pg_location2.second.equals(pg_location1.second)) {
                            interleavedPG.addTransition(new PGTransition<>(pg_location1, pg1_trans.getCondition(), pg1_trans.getAction(), pg_location2));
                        }
                    }
                }
            }
        }
        // Adding Transitions From PG2
        for (PGTransition<L2, A> pg2_trans : pg2.getTransitions()) {
            for (Pair<L1, L2> pg_location1 : interleavedPG.getLocations()) {
                if (pg_location1.second.equals(pg2_trans.getFrom())) {
                    for (Pair<L1, L2> pg_location2 : interleavedPG.getLocations()) {
                        if (pg_location2.second.equals(pg2_trans.getTo()) && pg_location2.first.equals(pg_location1.first)) {
                            interleavedPG.addTransition(new PGTransition<>(pg_location1, pg2_trans.getCondition(), pg2_trans.getAction(), pg_location2));
                        }
                    }
                }
            }
        }


        return interleavedPG;
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit
            (Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts = createTransitionSystem();

        //states init
        circuit_states_init(c, ts);

        // init initials
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : ts.getStates()) {
            if (!state.second.values().contains(Boolean.TRUE))
                ts.setInitial(state, true);
        }

        // init actions
        //pay attention, maybe need a deep copy here
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : ts.getStates()) {
            ts.addAction((state.first));
        }

        // init atomic proposition
        for (String reg : c.getRegisterNames())
            ts.addAtomicProposition(reg);
        for (String in : c.getInputPortNames())
            ts.addAtomicProposition(in);
        for (String out : c.getOutputPortNames())
            ts.addAtomicProposition(out);


        // init labels
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : ts.getStates()) {
            for (String reg : c.getRegisterNames())
                if (state.second.get(reg))
                    ts.addToLabel(state, reg);
            for (String in : c.getInputPortNames())
                if (state.first.get(in))
                    ts.addToLabel(state, in);
            for (String out : c.getOutputPortNames())
                if (c.computeOutputs(state.first, state.second).get(out))
                    ts.addToLabel(state, out);
        }

        // init transitions
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : ts.getStates()) {
            Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> transition;
            for (Map<String, Boolean> action : ts.getActions()) {
                Pair<Map<String, Boolean>, Map<String, Boolean>> toState = findStateCircuit(c, state, action, ts);
                transition = new Transition<>(state, action, toState);
                ts.addTransition(transition);
            }
        }

        // init name
        ts.setName("circuit to transition system");

        // remove unreachable
        remove_unreachable(ts);
        return ts;
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph
            (ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = new TransitionSystemImpl<>();
        ts.setName(pg.getName() + "_as_transition_system");

        Stack<Pair<L, Map<String, Object>>> to_work_on = new Stack<>();
        Set<Transition<Pair<L, Map<String, Object>>, A>> transitions = new HashSet<>();

        Set<Map<String, Object>> state_maps = new HashSet<>();
        for (List<String> initialization_list : pg.getInitalizations()) {
            Map<String, Object> state_map = new HashMap<>();
            for (String init_string : initialization_list) {
                for (ActionDef ad : actionDefs) {
                    if (ad.isMatchingAction(init_string)) {
                        state_map = ad.effect(state_map, init_string);
                    }
                }
            }
            state_maps.add(state_map);
        }
        if (state_maps.size() == 0) {
            state_maps.add(new HashMap<>());
        }

        for (Map<String, Object> state_map : state_maps) {
            for (L init_loc : pg.getInitialLocations()) {

                to_work_on.push(new Pair<>(init_loc, state_map));

                while (!to_work_on.empty()) {
                    Pair<L, Map<String, Object>> current_loc = to_work_on.pop();
                    for (PGTransition<L, A> pg_transition : pg.getTransitions()) {
                        if (pg_transition.getFrom().equals(current_loc.first)) {
                            if (ConditionDef.evaluate(conditionDefs, current_loc.second, pg_transition.getCondition())) {
                                Map<String, Object> new_state = current_loc.second;
                                for (ActionDef ad : actionDefs) {
                                    if (ad.isMatchingAction(pg_transition.getAction())) {
                                        new_state = ad.effect(current_loc.second, pg_transition.getAction());
                                        break;
                                    }
                                }
                                transitions.add(new Transition<>(new Pair<>(current_loc.first, current_loc.second), pg_transition.getAction(), new Pair<>(pg_transition.getTo(), new_state)));
                                if (!ts.getStates().contains(new Pair<>(pg_transition.getTo(), new_state))) {
                                    to_work_on.push(new Pair<>(pg_transition.getTo(), new_state));
                                }
                            }
                        }
                    }
                    Pair<L, Map<String, Object>> state_to_add = new Pair<>(current_loc.first, current_loc.second);
                    ts.addStates(state_to_add);
                    ts.addAtomicPropositions(current_loc.first.toString());
                    ts.addToLabel(state_to_add, current_loc.first.toString());
                    for (String key : current_loc.second.keySet()) {
                        ts.addAtomicPropositions(key + " = " + current_loc.second.get(key));
                        ts.addToLabel(state_to_add, key + " = " + current_loc.second.get(key));
                    }
                }
            }
        }


        for (Map<String, Object> state_map : state_maps) {
            for (L init_loc : pg.getInitialLocations()) {
                for (Pair<L, Map<String, Object>> state : ts.getStates()) {
                    if (state.first.equals(init_loc) && state.second.equals(state_map)) {
                        ts.setInitial(state, true);
                    }
                }
            }
        }


        for (Transition<Pair<L, Map<String, Object>>, A> transition : transitions) {
            ts.addAction(transition.getAction());
            ts.addTransition(transition);
        }

        return ts;
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem
            (ChannelSystem<L, A> cs) {

        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts = createTransitionSystem();


        List<ProgramGraph<L, A>> pgList = cs.getProgramGraphs();

        //states
        Set<Map<String, Object>> variables = make_variables_pgs(pgList);
        Set<List<L>> list_of_init_states = make_init_states_pgs(pgList);
        Set<Pair<List<L>, Map<String, Object>>> init_states = new HashSet<>();


        ActionDef async = new ParserBasedActDef();
        InterleavingActDef sync = new ParserBasedInterleavingActDef();
        ConditionDef cond = new ParserBasedCondDef();
        List<Transition<Pair<List<L>, Map<String, Object>>, A>> transitionList = new LinkedList<>();
        Set<Pair<List<L>, Map<String, Object>>> sawThem = new HashSet<>();

        for (List<L> l : list_of_init_states)
            for (Map<String, Object> m : variables)
                init_states.add(new Pair<>(l, m));


        for (Pair<List<L>, Map<String, Object>> state : init_states) {
            transitionList.addAll(recursive_transition(cs, state, 0, async, sync, cond, ts, sawThem));
        }

        for (Transition<Pair<List<L>, Map<String, Object>>, A> t : transitionList) {
            if (!ts.getStates().contains(t.getFrom()))
                ts.addState(t.getFrom());
            if (!ts.getStates().contains(t.getTo()))
                ts.addState(t.getTo());
            if (!ts.getActions().contains(t.getAction()))
                ts.addAction(t.getAction());
        }


        for (Pair<List<L>, Map<String, Object>> p : init_states) {
            ts.addState(p);
            ts.setInitial(p, true);
        }

        //atomic prop
        for (Pair<List<L>, Map<String, Object>> state : ts.getStates()) {
            for (L small_state : state.getFirst())
                ts.addAtomicProposition(small_state.toString());
            for (Map.Entry<String, Object> var_vals : state.getSecond().entrySet()) {
                ts.addAtomicProposition(var_vals.getKey() + " = " + var_vals.getValue().toString());
            }
        }
        return ts;
    }

    private <A, L> List<Transition<Pair<List<L>, Map<String, Object>>, A>> recursive_transition(ChannelSystem<L, A> cs, Pair<List<L>, Map<String, Object>> state, int index, ActionDef async, InterleavingActDef sync, ConditionDef cond, TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts, Set<Pair<List<L>, Map<String, Object>>> sawThem) {
        List<Transition<Pair<List<L>, Map<String, Object>>, A>> tranList = new LinkedList<>();
        if (index == cs.getProgramGraphs().size())
            return tranList;
        ProgramGraph<L, A> pg = cs.getProgramGraphs().get(index);
        for (PGTransition<L, A> transition : pg.getTransitions()) {
            if (state.getFirst().get(index).equals(transition.getFrom()))
                if (cond.evaluate(state.getSecond(), transition.getCondition())) {
                    String actionString = transition.getAction().toString();
                    String[] channel;
                    if (actionString.contains("!"))
                        channel = actionString.split("!");
                    else
                        channel = actionString.split("\\?");
                    if (sync.isOneSidedAction(transition.getAction().toString())) {
                        int index2 = 0;
                        for (ProgramGraph<L, A> pgs : cs.getProgramGraphs()) {
                            for (PGTransition<L, A> transition2 : pgs.getTransitions()) {
                                String actionString2 = transition.getAction().toString();
                                String[] channel2;
                                if (actionString2.contains("!"))
                                    channel2 = actionString2.split("!");
                                else
                                    channel2 = actionString2.split("\\?");
                                if ((actionString.contains("!") && actionString2.contains("?") && channel[0].equals(channel2[0])) ||
                                        (actionString.contains("?") && actionString2.contains("!") && channel[0].equals(channel2[0]))) {
                                    String newAction = channel[0];
                                    if (actionString.contains("!"))
                                        newAction = newAction.concat("!");
                                    else
                                        newAction = newAction.concat("?");
                                    newAction = newAction.concat(channel2[0]);
                                    List<L> myCopy = new LinkedList<>(state.getFirst());
                                    myCopy.set(index, transition.getTo());
                                    myCopy.set(index2, transition2.getTo());
                                    Pair<List<L>, Map<String, Object>> newState = new Pair<>(myCopy, sync.effect(state.getSecond(), (A) newAction));
                                    tranList.add(new Transition<>(state, (A) newAction, newState));
                                    tranList.addAll(recursive_transition(cs, newState, 0, async, sync, cond, ts, sawThem));
                                }
                            }
                            index2++;
                        }
                    } else {
                        List<L> myCopy = new LinkedList<>(state.getFirst());
                        myCopy.set(index, transition.getTo());
                        Pair<List<L>, Map<String, Object>> newState = new Pair<>(myCopy, async.effect(state.getSecond(), transition.getAction()));
                        if (newState.second != null) {
                            if (!sawThem.contains(newState)) {
                                sawThem.add(newState);
                                tranList.add(new Transition<>(state, transition.getAction(), newState));
                                tranList.addAll(recursive_transition(cs, newState, 0, async, sync, cond, ts, sawThem));
                            }

                        }

                    }
                }
        }
        tranList.addAll(recursive_transition(cs, state, index + 1, async, sync, cond, ts, sawThem));
        return tranList;
    }

    private <A, L> Set<Map<String, Object>> make_variables_pgs(List<ProgramGraph<L, A>> pgList) {

        Map<String, Set<Integer>> args = new HashMap<>();

        for (ProgramGraph<L, A> pg : pgList) {
            for (List<String> l : pg.getInitalizations()) {
                for (String s : l) {
                    String[] var_val = s.split(":=");
                    for (int i = 0; i < var_val.length; i++) {
                        var_val[i] = var_val[i].replaceAll("\\s+", "");
                    }
                    if (args.keySet().contains(var_val[0]))
                        args.get(var_val[0]).add(Integer.valueOf((var_val[1])));
                    else {
                        Set<Integer> mySet = new HashSet<>();
                        mySet.add(Integer.valueOf(var_val[1]));
                        args.put(var_val[0], mySet);
                    }
                }
            }
        }

        Set<Map<String, Object>> permotations = new HashSet<>();
        int size = args.size();

        Object[][] array_of_values = new Object[size][];

        String[] array_of_vars = new String[size];
        array_of_vars = args.keySet().toArray(array_of_vars);

        int[] bases = new int[size];
        int[] dynamic_number = new int[size];
        int size_all = 1;

        for (int i = 0; i < array_of_values.length; i++) {
            array_of_values[i] = args.get(array_of_vars[i]).toArray();
            bases[i] = array_of_values[i].length;
            dynamic_number[i] = 0;
            size_all = size_all * bases[i];
        }

        for (int i = 0; i < size_all; i++) {
            Map<String, Object> map = new HashMap<>();
            for (int j = 0; j < size; j++)
                map.put(array_of_vars[j], array_of_values[j][dynamic_number[j]]); //the i here might be j
            permotations.add(map);

            // update dynamic_number
            updateDynamicArray(size, bases, dynamic_number);
        }

        return permotations;
    }

    private void updateDynamicArray(int size, int[] bases, int[] dynamic_number) {
        boolean carry = true;
        for (int k = size - 1; k >= 0; k--) {
            if (carry && dynamic_number[k] + 1 == bases[k]) {
                carry = true;
                dynamic_number[k] = 0;
            } else {
                carry = false;
                dynamic_number[k] = dynamic_number[k] + 1;
            }
        }
    }

    private <L, A> Set<List<L>> make_states_pgs(List<ProgramGraph<L, A>> pgList) {

        Set<List<L>> state_list = new HashSet<>();
        int size = pgList.size();

        Object[][] array_of_locations = new Object[size][];
        int[] bases = new int[size];
        int[] dynamic_number = new int[size];
        int size_all = 1;

        for (int i = 0; i < array_of_locations.length; i++) {
            array_of_locations[i] = pgList.get(i).getLocations().toArray();
            bases[i] = array_of_locations[i].length;
            dynamic_number[i] = 0;
            size_all = size_all * bases[i];
        }

        for (int i = 0; i < size_all; i++) {
            List<L> state = new LinkedList<>();
            for (int j = 0; j < size; j++)
                state.add((L) array_of_locations[j][dynamic_number[j]]);
            state_list.add(state);

            // update dynamic_number
            updateDynamicArray(size, bases, dynamic_number);
        }

        return state_list;
    }

    private <L, A> Set<List<L>> make_init_states_pgs(List<ProgramGraph<L, A>> pgList) {

        Set<List<L>> state_list = new HashSet<>();
        int size = pgList.size();

        Object[][] array_of_locations = new Object[size][];
        int[] bases = new int[size];
        int[] dynamic_number = new int[size];
        int size_all = 1;

        for (int i = 0; i < array_of_locations.length; i++) {
            array_of_locations[i] = pgList.get(i).getInitialLocations().toArray();
            bases[i] = array_of_locations[i].length;
            dynamic_number[i] = 0;
            size_all = size_all * bases[i];
        }

        for (int i = 0; i < size_all; i++) {
            List<L> state = new LinkedList<>();
            for (int j = 0; j < size; j++)
                state.add((L) array_of_locations[j][dynamic_number[j]]);
            state_list.add(state);

            // update dynamic_number
            updateDynamicArray(size, bases, dynamic_number);
        }

        return state_list;
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product
            (TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        NanoPromelaParser.StmtContext sc = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
        return programGraphFromParsedNanoPromela(sc);
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        NanoPromelaParser.StmtContext sc = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        return programGraphFromParsedNanoPromela(sc);
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        NanoPromelaParser.StmtContext sc = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        return programGraphFromParsedNanoPromela(sc);
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

    private <STATE, ACTION, ATOMIC_PROPOSITION> void remove_unreachable(TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> ts) {
        Set<STATE> reachable_set = reach(ts);
        Set<STATE> unreachable_states = new HashSet<>();
        Set<Pair<STATE, ATOMIC_PROPOSITION>> ap_remove = new HashSet<>();
        Set<Transition<STATE, ACTION>> unreachable_transitions = new HashSet<>();

        for (STATE state : ts.getStates()) {
            if (!reachable_set.contains(state)) {
                Set<Transition<STATE, ACTION>> all = ts.getTransitions();
                for (Transition<STATE, ACTION> transition : all)
                    if (transition.getFrom().equals(state) || transition.getTo().equals(state))
                        unreachable_transitions.add(transition);
                unreachable_states.add(state);

                for (ATOMIC_PROPOSITION ap : ts.getLabelingFunction().get(state))
                    ap_remove.add(new Pair<>(state, ap));
            }
        }

        for (Transition<STATE, ACTION> transition : unreachable_transitions)
            ts.removeTransition(transition);

        for (Pair<STATE, ATOMIC_PROPOSITION> p : ap_remove)
            ts.removeLabel(p.first, p.second);

        for (STATE state : unreachable_states) {
            ts.removeState(state);
        }
    }

    private Pair<Map<String, Boolean>, Map<String, Boolean>> findStateCircuit(Circuit
                                                                                      c, Pair<Map<String, Boolean>,
            Map<String, Boolean>> state, Map<String, Boolean> action, TransitionSystem<Pair<Map<String, Boolean>,
            Map<String, Boolean>>, Map<String, Boolean>, Object> ts) {
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state_in_ts : ts.getStates()) {
            if (c.updateRegisters(state.first, state.second).equals(state_in_ts.second) &&
                    action.equals(state_in_ts.first))
                return state_in_ts;
        }
        return null; //should not ever happen
    }

    private void circuit_states_init(Circuit
                                             c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts) {
        // init regs
        Set<Map<String, Boolean>> reg = new HashSet<>();
        String[] regs = new String[c.getRegisterNames().size()];
        regs = c.getRegisterNames().toArray(regs);
        circuit_create_map_states(reg, regs);

        // init ins
        Set<Map<String, Boolean>> in = new HashSet<>();
        String[] inputs = new String[c.getInputPortNames().size()];
        inputs = c.getInputPortNames().toArray(inputs);
        circuit_create_map_states(in, inputs);

        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> combined = s1_x_s2(in, reg);
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> p : combined)
            ts.addState(p);
    }

    private void circuit_create_map_states(Set<Map<String, Boolean>> set, String[] names) {
        int size = (int) Math.pow(2, names.length);

        for (int i = 0; i < size; i++) {
            Map<String, Boolean> map_i = new HashMap<>();
            StringBuilder binStr = new StringBuilder(Integer.toBinaryString(i));
            int zero_to_add = names.length - binStr.length();
            for (int j = 0; j < zero_to_add; j++)
                binStr.insert(0, "0");
            for (int j = 0; j < names.length; j++) {
                map_i.put(names[j], binStr.charAt(j) == '0' ? Boolean.FALSE : Boolean.TRUE);
            }
            set.add(map_i);
        }
    }

    private <S1, S2, A, P> void interleave_initTransitionFunction_handShakingActions
            (TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem, Set<A> handShakingActions) {

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
            (TransitionSystem<Pair<S1, S2>, A, P> interleaveTransitionSystem, Set<S1> states, Set<S2> states2, boolean isInitial) {
        Set<Pair<S1, S2>> interleaveStates = s1_x_s2(states, states2);
        for (Pair<S1, S2> s : interleaveStates) {
            interleaveTransitionSystem.addState(s);
            if (isInitial)
                interleaveTransitionSystem.setInitial(s, true);
        }
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
        interleave_initStates(interleaveTransitionSystem, ts1.getStates(), ts2.getStates(), false);

        // init initials
        interleave_initStates(interleaveTransitionSystem, ts1.getInitialStates(), ts2.getInitialStates(), true);

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

    private <S, A, P> AlternatingSequence<S, A> compareASandTS
            (TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> next) {
        S stateFrom;
        A action;
        S stateTo;

        if (next.tail().isEmpty()) {
            if (ts.getStates().contains(next.head())) {
                return next;
            }
        }
        AlternatingSequence<A, S> tail = next.tail();
        while (!next.tail().isEmpty()) {
            stateFrom = next.head();
            action = next.tail().head();
            stateTo = next.tail().tail().head();
            if (!ts.getStates().contains(stateFrom)) {
                throw new StateNotFoundException(stateFrom);
            } else if (!ts.getStates().contains(stateTo)) {
                throw new StateNotFoundException(stateTo);
            } else if (!ts.getActions().contains(action)) {
                throw new ActionNotFoundException(action);
            }

            if (!ts.getTransitions().contains(new Transition<>(stateFrom, action, stateTo))) { //TODO: not sure if contains will perform deep compare
                return null;
            }
            next = next.tail().tail();
        }

        return next;
    }


    private ProgramGraph<String, String> programGraphFromParsedNanoPromela(NanoPromelaParser.StmtContext tree) {
        ProgramGraphImpl<String, String> pg = new ProgramGraphImpl<>();
        return eliminateUnreachableLocations(connectLocations(pg, sub(tree), tree));
    }

    private Set<ParserRuleContext> sub(ParserRuleContext tree) {
        Set<ParserRuleContext> locations = new HashSet<>();

        if (tree.children == null) { //Try to remove this and see if it's still working.
            return locations;
        }

        if (tree instanceof NanoPromelaParser.StmtContext) {
            NanoPromelaParser.StmtContext casted_child = (NanoPromelaParser.StmtContext) tree;
            Set<ParserRuleContext> sub_stmt1 = sub((ParserRuleContext) casted_child.children.get(0));
            if (casted_child.children.size() == 3) {
                if (((NanoPromelaParser.StmtContext) casted_child.children.get(2)).children != null) {
                    Set<ParserRuleContext> sub_stmt2 = sub((ParserRuleContext) casted_child.children.get(2));
                    for (ParserRuleContext loc : sub_stmt1) {
                        NanoPromelaParser.StmtContext sc = new NanoPromelaParser.StmtContext(null, 71);
                        NanoPromelaParser.StmtContext loc_sc = new NanoPromelaParser.StmtContext(sc, 71);
                        loc_sc.addChild(loc);
                        sc.addChild(loc_sc);
                        sc.addChild(new TerminalNodeImpl(new CommonToken(0, ";")));
                        sc.addChild((RuleContext) casted_child.children.get(2));
                        //locations.add(loc+";"+casted_child.children.get(2).getText());
                        locations.add(sc);
                        locations.addAll(sub_stmt2);
                    }
                } else {
                    locations.addAll(sub_stmt1);
                }
            } else {
                locations.addAll(sub_stmt1);
            }
        } else if (tree instanceof NanoPromelaParser.IfstmtContext) {
            for (int i = 1; i < tree.children.size() - 1; i++) {
                locations.addAll(sub((ParserRuleContext) ((NanoPromelaParser.IfstmtContext) tree).children.get(i)));
            }
            locations.add(tree);
            //locations.add("");
        } else if (tree instanceof NanoPromelaParser.DostmtContext) {
            locations.add(tree);
            //locations.add("");
            for (int i = 1; i < tree.children.size() - 1; i++) {
                Set<ParserRuleContext> result = sub((ParserRuleContext) ((NanoPromelaParser.DostmtContext) tree).children.get(i));
                for (ParserRuleContext loc : result) {
                    NanoPromelaParser.StmtContext sc = new NanoPromelaParser.StmtContext(null, 71);
                    NanoPromelaParser.StmtContext loc_sc = new NanoPromelaParser.StmtContext(sc, 71);
                    loc_sc.addChild(loc);
                    sc.addChild(loc_sc);
                    sc.addChild(new TerminalNodeImpl(new CommonToken(0, ";")));
                    sc.addChild(tree);

                    //locations.add(loc+";"+tree.getText());
                    locations.add(sc);
                }
            }
        } else if (tree instanceof NanoPromelaParser.AssstmtContext) {
            //locations.add("");
            locations.add(tree);
        } else if (tree instanceof NanoPromelaParser.ChanreadstmtContext) {
            //locations.add("");
            locations.add(tree);
        } else if (tree instanceof NanoPromelaParser.ChanwritestmtContext) {
            //locations.add("");
            locations.add(tree);
        } else if (tree instanceof NanoPromelaParser.SkipstmtContext) {
            //locations.add("");
            locations.add(tree);
        } else if (tree instanceof NanoPromelaParser.AtomicstmtContext) {
            //locations.add("");
            locations.add(tree);
        } else if (tree instanceof NanoPromelaParser.OptionContext) {
            locations.addAll(sub((ParserRuleContext) ((NanoPromelaParser.OptionContext) tree).children.get(3)));
        }

        return locations;
    }

    private ProgramGraph<String, String> connectLocations(ProgramGraph<String, String> pg, Set<ParserRuleContext> sub, NanoPromelaParser.StmtContext tree) {
        pg.setName("");
        pg.addLocation("");
        for (ParserRuleContext loc : sub) {
            pg.addLocation(loc.getText());
            Set<PGTransition<String, String>> transitions = inferTransition(loc);
            for (PGTransition<String, String> transition : transitions) {
                pg.addTransition(transition);
            }
        }
        pg.setInitial(tree.getText(), true);
        return pg;
    }

    private Set<PGTransition<String, String>> inferTransition(ParserRuleContext loc) {
        Set<PGTransition<String, String>> transitions = new HashSet<>();
        Pair<String, String> cond_act;
        if ((cond_act = canTransitToExit(loc)) != null) {
            transitions.add(new PGTransition<>(loc.getText(), cond_act.first, cond_act.second, ""));
        } else if (loc instanceof NanoPromelaParser.StmtContext && loc.children.size() == 1 && ((cond_act = canTransitToExit((ParserRuleContext) loc.children.get(0))) != null)) {
            transitions.add(new PGTransition<>(loc.getText(), cond_act.first, cond_act.second, ""));
        }
        if (loc.children.size() == 1 && loc instanceof NanoPromelaParser.StmtContext) {
            Set<PGTransition<String, String>> inferred_transitions = inferTransition((ParserRuleContext) loc.children.get(0));
            transitions.addAll(inferred_transitions);
        } else if (loc.children.get(0) instanceof NanoPromelaParser.StmtContext) {
            if (((ParserRuleContext) loc.children.get(2)).children != null) {
                Set<PGTransition<String, String>> inferred_transitions = inferTransition((ParserRuleContext) loc.children.get(0));
                for (PGTransition<String, String> inferred_transition : inferred_transitions) {
                    if (inferred_transition.getTo().equals("")) {
                        transitions.add(new PGTransition<>(loc.getText()
                                , inferred_transition.getCondition(), inferred_transition.getAction(), loc.children.get(2).getText()));
                    } else {
                        transitions.add(new PGTransition<>(loc.getText(), inferred_transition.getCondition(),
                                inferred_transition.getAction(), inferred_transition.getTo() + ";" + loc.children.get(2).getText()));
                    }
                }
            } else {
                Set<PGTransition<String, String>> inferred_transitions = inferTransition((ParserRuleContext) loc.children.get(0));
                transitions.addAll(inferred_transitions);
            }

        } else if (loc instanceof NanoPromelaParser.IfstmtContext) {
            for (int i = 1; i < ((NanoPromelaParser.IfstmtContext) loc).children.size() - 1; i++) {
                NanoPromelaParser.OptionContext option_context =
                        (NanoPromelaParser.OptionContext) ((NanoPromelaParser.IfstmtContext) loc).children.get(i);
                Set<PGTransition<String, String>> inferred_transitions = inferTransition((ParserRuleContext) option_context.children.get(3));
                for (PGTransition<String, String> inferred_transition : inferred_transitions) {
                    transitions.add(new PGTransition<>(loc.getText(), "(" + option_context.children.get(1).getText() + ")" + (inferred_transition.getCondition().equals("") ? "" : (" && (" + inferred_transition.getCondition() + ")")),
                            inferred_transition.getAction(), inferred_transition.getTo()));
                }
            }
        } else if (loc instanceof NanoPromelaParser.DostmtContext) {
            for (int i = 1; i < ((NanoPromelaParser.DostmtContext) loc).children.size() - 1; i++) {
                NanoPromelaParser.OptionContext option_context =
                        (NanoPromelaParser.OptionContext) ((NanoPromelaParser.DostmtContext) loc).children.get(i);
                Set<PGTransition<String, String>> inferred_transitions = inferTransition((ParserRuleContext) option_context.children.get(3));
                for (PGTransition<String, String> inferred_transition : inferred_transitions) {
                    if (inferred_transition.getTo().equals("")) {
                        transitions.add(new PGTransition<>(loc.getText(), "(" + option_context.children.get(1).getText() + ")" + (inferred_transition.getCondition().equals("") ? "" : (" && (" + inferred_transition.getCondition() + ")")),
                                inferred_transition.getAction(), loc.getText()));
                    } else {
                        transitions.add(new PGTransition<>(loc.getText(), "(" + option_context.children.get(1).getText() + ")" + (inferred_transition.getCondition().equals("") ? "" : (" && (" + inferred_transition.getCondition() + ")")),
                                inferred_transition.getAction(), inferred_transition.getTo() + ";" + loc.getText()));
                    }
                }
            }
        }

        return transitions;
    }

    private Pair<String, String> canTransitToExit(ParserRuleContext stmt) {
        if (stmt instanceof NanoPromelaParser.SkipstmtContext) return new Pair<>("", stmt.getText());
        else if (stmt instanceof NanoPromelaParser.AssstmtContext) return new Pair<>("", stmt.getText());
        else if (stmt instanceof NanoPromelaParser.ChanwritestmtContext) return new Pair<>("", stmt.getText());
        else if (stmt instanceof NanoPromelaParser.ChanreadstmtContext) return new Pair<>("", stmt.getText());
        else if (stmt instanceof NanoPromelaParser.AtomicstmtContext) return new Pair<>("", stmt.getText());
        else if (stmt instanceof NanoPromelaParser.DostmtContext) {
            StringBuilder condition = new StringBuilder();
            NanoPromelaParser.DostmtContext do_stmt = (NanoPromelaParser.DostmtContext) stmt;
            for (int i = 1; i < do_stmt.children.size() - 1; i++) {
                condition.append("!((").append(((NanoPromelaParser.OptionContext) do_stmt.children.get(i)).children.get(1).getText()).append(")) && ");
            }
            return new Pair<>(condition.substring(0, condition.length() - 4), "");
        }
        return null;
    }

    private ProgramGraph<String, String> eliminateUnreachableLocations(ProgramGraph<String, String> pg) {

        Set<String> reachableLocations = new HashSet<>();
        Set<String> currentlyDiscovering = new HashSet<>();
        Stack<String> workStack = new Stack<>();

        for (String loc : pg.getInitialLocations()) {
            workStack.push(loc);
            currentlyDiscovering.add(loc);
            while (!workStack.empty()) {
                String currLocation = workStack.pop();
                reachableLocations.add(currLocation);
                currentlyDiscovering.remove(currLocation);
                Set<String> nextLocations = post(pg, currLocation);
                for (String nextLocation : nextLocations) {
                    if (currentlyDiscovering.contains(nextLocation) || reachableLocations.contains(nextLocation)) {
                        continue;
                    }
                    workStack.push(nextLocation);
                }
            }
        }
        Set<String> locations_to_remove = new HashSet<>();
        for (String loc : pg.getLocations()) {
            if (!reachableLocations.contains(loc)) {
                Set<PGTransition<String, String>> transitions_to_remove = new HashSet<>();
                for (PGTransition<String, String> pg_transition : pg.getTransitions()) {
                    if (pg_transition.getFrom().equals(loc) || pg_transition.getTo().equals(loc)) {
                        transitions_to_remove.add(pg_transition);
                    }
                }
                for (PGTransition<String, String> transition_to_remove : transitions_to_remove) {
                    pg.removeTransition(transition_to_remove);
                }
                locations_to_remove.add(loc);
            }
        }
        for (String location_to_remove : locations_to_remove) {
            pg.removeLocation(location_to_remove);
        }

        return pg;
    }


    public Set<String> post(ProgramGraph<String, String> pg, String location) {
        Set<String> post_locations = new HashSet<>();
        for (PGTransition<String, String> transition : pg.getTransitions()) {
            if (transition.getFrom().equals(location))
                post_locations.add(transition.getTo());
        }
        return post_locations;
    }
}
