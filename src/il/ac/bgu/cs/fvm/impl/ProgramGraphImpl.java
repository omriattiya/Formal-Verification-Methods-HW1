package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.util.Pair;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {
    private String name;
    private Set<L> locations;
    private Set<A> actions;
    private Set<L> initials;
    private Set<PGTransition<L, A>> transitions;
    private Set<List<String>> initializations;

    public ProgramGraphImpl(String name) {
        this.name = name;
        locations = new HashSet<>();
        actions = new HashSet<>();
        initials = new HashSet<>();
        transitions = new HashSet<>();
        initializations = new HashSet<>();
    }

    @Override
    public void addInitalization(List<String> init) {
        initializations.add(init);
        /*for (String var : init) {
            String[] var_val = var.split(":=");
            for (int i = 0; i < var_val.length; i++) {
                var_val[i] = var_val[i].replaceAll("\\s+", "");
            }
            for(Pair<String, String> vv: vars_vals){
                if (vv.first.equals(var_val[0])) {
                    vars_vals.remove(vv);
                }
            }
            vars_vals.add(new Pair<>(var_val[0],var_val[1]));
        }*/
    }

    @Override
    public void setInitial(L location, boolean isInitial) throws IllegalArgumentException {
        if (!locations.contains(location)) {
            throw new IllegalArgumentException("" + location);
        }
        if (isInitial) {
            initials.add(location);
        } else {
            initials.remove(location);
        }
    }

    @Override
    public void addLocation(L l) {
        locations.add(l);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        transitions.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return initializations;
    }

    @Override
    public Set<L> getInitialLocations() {
        return initials;
    }

    @Override
    public Set<L> getLocations() {
        return locations;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return transitions;
    }

    @Override
    public void removeLocation(L l) {
        locations.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        transitions.remove(t);
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
