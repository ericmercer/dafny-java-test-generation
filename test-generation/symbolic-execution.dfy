class Token {
  var fingerprint : int;
  var clearance : int;  

  var valid : bool;

  predicate isValidFingerprintPredicate(fingerprint : int) 
  reads this`valid, this`fingerprint
  {
    (valid == true && fingerprint == this.fingerprint)
  }

  method isValidFingerprint(fingerprint : int) returns (result : bool)
  ensures valid == old(isValidFingerprintPredicate(fingerprint))
  ensures result == valid
  modifies this`valid
  {
    valid := (valid == true && fingerprint == this.fingerprint);
    result := valid;
  }

  method isValidToken() returns (result : bool)
  ensures result == valid
  {
    result := valid;
  }

  function getClearanceFunction() : int
  reads this`clearance
  {
    this.clearance
  }
  method getClearance() returns (result : int)
  ensures result == clearance
  {
    result := clearance;
  }
}

datatype ResourceState = Open | Closed

class IdStation {
  var securityLevel : int;
  var alarm : bool
  var state : ResourceState

  method open(token : Token, fingerprint : int)
  requires alarm == false && state == Closed 
  ensures alarm == !old(token.isValidFingerprintPredicate(fingerprint))
  ensures if (!alarm && old(token.getClearanceFunction() >= securityLevel)) 
    then state == Open else state == old(state)
  modifies token, this`alarm, this`state
  {
    var isValidFingerprint := token.isValidFingerprint(fingerprint);
    alarm := !isValidFingerprint;
    
    var clearance := token.getClearance();
    if (!alarm && clearance >= securityLevel) {
      state := Open;
    }
  }

  // Two paths to consider with each written as a straight line program
  method openPathOne(token : Token, fingerprint : int)
  requires alarm == false && state == Closed 
  ensures alarm == !old(token.isValidFingerprintPredicate(fingerprint))
  ensures if (!alarm && old(token.getClearanceFunction() >= securityLevel)) 
    then state == Open else state == old(state)
  modifies token, this`alarm, this`state
  {
    var isValidFingerprint := token.isValidFingerprint(fingerprint);
    alarm := !isValidFingerprint;
    
    var clearance := token.getClearance();
    assume(!alarm && clearance >= securityLevel);
    state := Open;  
  }

  // In general: 
  // A <== the requires
  // G <== the ensures
  
  // Idea 1: Satisfiablility Modulo Theories Approach
  // 
  // Treat all methods as uninterpreted functions. Find the satisfying
  // assignment. Then solve the constraint problems as independently 
  // as possible.
  method openPathOne(token : Token, fingerprint : int)
  requires alarm == false && state == Closed 
  ensures alarm == !old(token.isValidFingerprintPredicate(fingerprint))
  ensures if (!alarm && old(token.getClearanceFunction() >= securityLevel)) 
    then state == Open else state == old(state)
  modifies token, this`alarm, this`state
  {
    // Symbolic variables:
    // alarm: (1)
    // state: (2)
    // token.isValidFingerprint(fingerprint): (3)
    // token.getClearance(): (4)
    // token.isValidFingerprintPredicate(fingerprint): (5)
    // token.getClearanceFunction(): (6)
    // securityLevel: (7)
    // fingerprint: (8)

    // requires
    // pc: (1) = false /\ (2) = Closed

    var isValidFingerprint := token.isValidFingerprint(fingerprint);
    // pc: (1) = false /\ (2) = Closed
    // isValidFingerPrint: (3)

    alarm := !isValidFingerprint;
    // pc: (1) = false /\ (2) = Closed
    // isValidFingerPrint: (3)
    // alarm: !(3)

    var clearance := token.getClearance();
    // pc: (1) = false /\ (2) = Closed
    // isValidFingerPrint: (3)
    // alarm: !(3)
    // clearance: (4)

    assume(!alarm && clearance >= securityLevel);
    // pc: (1) = false /\ (2) = Closed /\ (3) /\ (4) >= (7)
    
    state := Open;
    // pc: (1) = false /\ (2) = Closed /\ (3) /\ (4) >= (7)
    // isValidFingerPrint: (3)
    // alarm: !(3)
    // clearance: (4)
    // state: Open
    
    // pc:
    //    (1) = false 
    // /\ (2) = Closed 
    // /\ (3) 
    // /\ (4) >= (7)
    //
    // SAT: !(1), (2) = Closed, (3), (4) >= 7

    // (3)  ensures token.valid == old(tokon.isValidFingerprintPredicate(fingerprint))
    //      ensures result == valid
    // (5)  (token.valid == true && fingerprint == this.fingerprint)
    // 

    // ensures (refer to original symbol table for 'old')
    //
    // ensures alarm == !old(token.isValidFingerprintPredicate(fingerprint))
    // ensures if (!alarm && old(token.getClearanceFunction() >= securityLevel)) 
    //   then state == Open else state == old(state)
    //
    //    !(3) = !(5)
    // /\ (((3) /\ (6) >= (7)) -> Open == Open)
    // /\ (!((3) /\ (6) >= (7)) -> Open == (2))
    
  }
  
  // Ignore Path 2 for now to talk about 
  method openPathTwo(token : Token, fingerprint : int)
  requires alarm == false && state == Closed 
  ensures alarm == !old(token.isValidFingerprintPredicate(fingerprint))
  ensures if (!alarm && old(token.getClearanceFunction() >= securityLevel)) 
    then state == Open else state == old(state)
  modifies token, this`alarm, this`state
  {
    var isValidFingerprint := token.isValidFingerprint(fingerprint);
    alarm := !isValidFingerprint;
    
    var clearance := token.getClearance();
    assume(!(!alarm && clearance >= securityLevel));
  }
}

