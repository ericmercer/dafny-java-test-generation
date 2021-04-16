class T {
  var f : int;
  var l : int;  
  var v : bool;

  function method isF(f : int) : bool
  reads `v, `f
  {
    (v && f == this.f)
  }

  method setV(f : int) 
  ensures v == old(isF(f))
  modifies `v
  {
    v := isF(f);
  }

  function method getL() : int
  reads `l
  {
    l
  }
}

datatype R = O | C | D

class I {
  var a : bool;
  var l : int;
  var s : R;

  method o(t : T, f : int)
  requires !a && (s == C)
  ensures (a == !old(t.isF(f)))
  ensures if (!a && l >= t.getL()) then 
            s == O 
          else 
            s == old(s)
  modifies t, `a, `s
  {
    a := !t.isF(f);
    if (!a && l >= t.getL()) {
      s := O;
    }
  }
}

class I_truePath {
  var a : bool;
  var l : int;
  var s : R;

  method o(t : T, f : int)
  requires !a && (s == C)
  ensures (a == !old(t.isF(f)))
  ensures if (!a && l >= t.getL()) then 
            s == O 
          else 
            s == old(s)
  modifies t, `a, `s
  {
    // Table 0 -- "old"
    // a: a_0
    // l: l_0
    // s: s_0
    // t.isF(f): t.isF_0
    // t.getL(): t.getL_0

    // pc: !a_0 && (s_0 == C)

    a := !t.isF(f);
    // a: !t.isF_0

    assume (!a && l >= t.getL());
    // pc: !a_0 && (s_0 == C) && t.isF_0 && (l >= t.getL_0)

    s := O;
    // s := 0
  }
}

// SAT(pc): a = false, s = C, l = 0, t.isF(f) = true, t.getL() = 0
method testOpaque() {
  var i: I := new I;
  i.a := false;
  i.l := 0;
  i.s := C;
  var t: T := new T;
  var f: int;
  assume (t.isF(f) == true);
  assume (t.getL() == 0);
  var old_s := i.s;
  i.o(t, f);
  assert (if (!i.a && i.l >= t.getL()) then i.s == O else i.s == old_s);
}

// 1) Everything is uninterpreted
// 2) If a method is called with a modifies clause, then a new symbolic variable is required
// 3) Capture all "old" values in any ensures to use in the assert
// 4) Use mocks for Java tests
// 5) Potentially tests unreachable paths

// Is the method a sound over-approximation of statement-level branch coverage?
// What if a branch in explored via a non-feasible path?

// If a test fails, then the test must be refined as the path may be unreachable.

// Dafny gives everything needed to generate the over-approximated set of tests