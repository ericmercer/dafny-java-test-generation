class T {
  var f : int; var l : int;  var v : bool;

  function method isF(f : int) : bool
  reads `f, `v { (v && (f == this.f)) }

  function method getL() : int
  reads `l { l }

  method setV(f : int)
  ensures v == old(isF(f))
  modifies `v {
    v := isF(f);
  }

}


class I {
  var a : bool; var s : bool; var l : int;

  method o(t : T, f : int)
  requires !a && !s
  ensures s == (old(t.isF(f)) && l >= t.getL())
  ensures !(old(t.isF(f)) && l >= t.getL()) ==> (a == t.isF(f))
  modifies t, `a, `s
  {
    if (t.isF(f) && l >= t.getL()) {
      s := true;
    } else {
      s := false;
      t.setV(f);
      a := t.isF(f);
    }
  }

  method o_path0(t : T, f : int)
  requires !a && !s
  ensures s == (old(t.isF(f)) && l >= t.getL())
  ensures !(old(t.isF(f)) && l >= t.getL()) ==> (a == t.isF(f))
  modifies t, `a, `s
  {
    assume (t.isF(f));
    assume (l >= t.getL());
    s := true;
    // pc: !a_0 /\ !s_0 /\ t.isF_0 /\ l_0 >= t.getL_0
  }

  method o_path1(t : T, f : int)
  requires !a && !s
  ensures s == (old(t.isF(f)) && l >= t.getL())
  ensures !(old(t.isF(f)) && l >= t.getL()) ==> (a == t.isF(f))
  modifies t, `a, `s
  {
    assume (t.isF(f));
    assume !(l >= t.getL());
    s := false;
    t.setV(f);
    a := t.isF(f);
    // pc: !a_0 /\ !s_0 /\ t.isF_0 /\ !(l_0 >= t.getL_0)
  }

  method o_path2(t : T, f : int)
  requires !a && !s
  ensures s == (old(t.isF(f)) && l >= t.getL())
  ensures !(old(t.isF(f)) && l >= t.getL()) ==> (a == t.isF(f))
  modifies t, `a, `s
  {
    assume(!t.isF(f));
    s := false;
    t.setV(f);
    a := t.isF(f);
  }
}


// pc: pc: !a_0 /\ !s_0 /\ t.isF_0 /\ l_0 >= t.getL_0
// SAT(pc): a = false, s = false, l == 0, t.isF(f) == true, t.getL() = 0
//
// Important: no side-effects in contract but still need to capture since the method
// side-effect and change the later call
method test_path0() {
  var i: I := new I;
  i.a := false;
  i.s := false;
  i.l := 0;
  var t: T := new T;
  var f: int;
  assume (t.isF(f));
  assume (t.getL() == 0);
  var old_isF := t.isF(f);
  i.o(t, f);
  assert(i.s == (old_isF && i.l >= t.getL()));
  assert(!(old_isF && i.l >= t.getL()) ==> (i.a == t.isF(f)));
}

// pc: !a_0 /\ !s_0 /\ t.isF_0 /\ !(l_0 >= t.getL_0)
// SAT(pc): a = false, s = false, l == 0, t.isF(f) == true, t.getL() = 0
// Dependency: t.isF(f) (see frame for t.setV(f))
// SAT(t.v && (f == t.f)): t.v = true, t.f = 0, f = 0 (l is unconstrained)
method test_path1() {
   var i: I := new I;
  i.a := false;
  i.s := false;
  i.l := 0;
  var t: T := new T;
  t.v := true;
  t.f := 0;
  var f: int := 0;
  assert (t.isF(f));
  assume (t.getL() == 0);
  var old_isF := t.isF(f);
  i.o(t, f);
  assert(i.s == (old_isF && i.l >= t.getL()));
  assert(!(old_isF && i.l >= t.getL()) ==> (i.a == t.isF(f)));
}