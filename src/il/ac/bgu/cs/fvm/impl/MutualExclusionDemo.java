package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.examples.PetersonProgramGraphBuilder;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.Util;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;

public class MutualExclusionDemo
{
    private static FvmFacade fvmFacadeImpl = new FvmFacadeImpl();

    public static void main(String[] args){
        System.out.println("Welcome to our live demonstration:");
        System.out.println("Here we go: \n");


        System.out.println("Building 2 program graphs representing each process in peter's mutual exclusion algorithm, P1 and P2");
        ProgramGraph<String, String> pg1 = PetersonProgramGraphBuilder.build(1);
        ProgramGraph<String, String> pg2 = PetersonProgramGraphBuilder.build(2);

        System.out.println("Interleaving the 2 graphs, P1 || P2");
        ProgramGraph<Pair<String, String>, String> pg = fvmFacadeImpl.interleave(pg1, pg2);

        Set<ActionDef> ad = set(new ParserBasedActDef());
        Set<ConditionDef> cd = set(new ParserBasedCondDef());

        TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts;

        System.out.println("Transforming the interleaved graphs into one transition system");
        ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);


        addLabels(ts);

        System.out.println("Verifying mutual exclusion");

        {
            Set<Set<String>> all = Util.powerSet(ts.getAtomicPropositions());

            Predicate<Set<String>> phi = a -> a.contains("crit1") && a.contains("crit2");

            Automaton<String, String> aut1 = new Automaton<>();

            all.stream().filter(phi.negate()).forEach(l -> aut1.addTransition("q0", l, "q0"));
            all.stream().filter(phi).forEach(l -> aut1.addTransition("q0", l, "q1"));
            all.stream().forEach(l -> aut1.addTransition("q1", l, "q1"));

            aut1.setInitial("q0");
            aut1.setAccepting("q1");

            VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr1 = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut1);
            System.out.println("verification result type : " + vr1.getClass());
        }


        System.out.println("Verifying the liveness of each process");

        {
            Set<Set<String>> all = Util.powerSet(ts.getAtomicPropositions());

            Predicate<Set<String>> phi1 = a -> a.contains("wait1");
            Predicate<Set<String>> phi2 = a -> !a.contains("crit1");

            Automaton<String, String> aut2 = new Automaton<>();

            all.stream().forEach(l -> aut2.addTransition("q0", l, "q0"));
            all.stream().filter(phi1).forEach(l -> aut2.addTransition("q0", l, "q1"));
            all.stream().filter(phi2).forEach(l -> aut2.addTransition("q1", l, "q1"));

            aut2.setInitial("q0");
            aut2.setAccepting("q1");

            VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr2 = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut2);
            System.out.println("verification result type : " + vr2.getClass());
        }


    }


    private static void addLabels(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        ts.getStates().stream().forEach(st -> ts.getAtomicPropositions().stream().forEach(ap -> ts.removeLabel(st, ap)));

        Set<String> aps = new HashSet<>(ts.getAtomicPropositions());
        aps.stream().forEach(ap -> ts.removeAtomicProposition(ap));

        seq("wait1", "wait2", "crit1", "crit2", "crit1_enabled").stream().forEach(s -> ts.addAtomicPropositions(s));

        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("crit1")).forEach(s -> ts.addToLabel(s, "crit1"));
        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("wait1")).forEach(s -> ts.addToLabel(s, "wait1"));

        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("crit2")).forEach(s -> ts.addToLabel(s, "crit2"));
        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("wait2")).forEach(s -> ts.addToLabel(s, "wait2"));

        Predicate<Pair<Pair<String, String>, ?>> _crit1 = ss -> ss.getFirst().getFirst().equals("crit1");
        ts.getStates().stream().filter(s -> fvmFacadeImpl.post(ts, s).stream().anyMatch(_crit1)).forEach(s -> ts.addToLabel(s, "crit1_enabled"));
    }
}
