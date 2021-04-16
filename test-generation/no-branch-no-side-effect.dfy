class T {
  var f : int;

  function method isF(f : int) : bool
  reads `f
  {
    (f == this.f)
  }

}

class I {
  var s : bool;
  var a : bool;

  method o(t : T, f : int)
  requires !s && !a
  ensures (s == t.isF(f)) && (a == !s) 
  modifies `s, `a
  {
    var isF := t.isF(f);
    a := !isF;
    
    if (!a) {
      s := true;
    }
  }
}

class I_truePath {
  var s : bool;
  var a : bool;

  method o(t : T, f : int)
  requires !s && !a
  ensures (s == t.isF(f)) && (a == !s) 
  modifies `s, `a
  {
    // Table 0 -- "old"
    // s: s_0
    // a: a_0
    // t: t_0
    // f: f_0
    // t.isF(f): t.isF_0 (depends on t_0 and f_0)

    // pc: !s_0 /\ !a_0

    var isF := t.isF(f);
    // isF: t.isF_0

    a := !isF;
    // a: !(t.isF_0)

    assume(!a);
    // pc: !s_0 /\ !a_0 /\ !(t.isF_0)

    s := true;
    // s: true

  }
}

// SAT(pc): s = false, a = false, t.isF(f) = true
method testOpaque() {
  var i: I := new I;
  i.s := false;
  i.a := false;
  var t: T := new T;
  var f: int;
  assume (t.isF(f) == true);
  i.o(t, f);
  assert (i.s == t.isF(f)) && (i.a == !i.s);
}

// SAT(pc): s = false, a = false, t.isF(f) = true
// Solve t.isF(f)
// SAT(f == this.f): f = 0, this.f = 0
method testFlattened() {
  var i: I := new I;
  i.s := false;
  i.a := false;
  var t: T := new T;
  t.f := 0;
  var f: int := 0;
  i.o(t, f);
  assert (i.s == t.isF(f)) && (i.a == !i.s);
}