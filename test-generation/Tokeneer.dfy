class Token {
  var fingerprint : int;
  var clearance : int;  

  var valid : bool;

  predicate matches(fingerprint : int, clearance : int, valid : bool)
  reads this`fingerprint, this`clearance, this`valid
  {
       fingerprint == this.fingerprint
    && clearance == this.clearance
    && valid == this.valid
  }

  constructor (fingerprint : int, clearance : int)
  requires clearance in {0, 1, 2} 
  ensures this.fingerprint == fingerprint && this.clearance == clearance && valid == true
  {
    this.fingerprint := fingerprint;
    this.clearance := clearance;
    valid := true;
  }

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

class EnrollementStation {
  var issuedTokens : set<int>;

  constructor ()
  ensures issuedTokens == {}
  {
    issuedTokens := {};
  }

  method getToken(fingerprint : int, clearance : int) returns (token : Token?)
  requires clearance in {0, 1 , 2}
  ensures old(fingerprint in issuedTokens) ==> (token == null && issuedTokens == old(issuedTokens))
  ensures old(fingerprint !in issuedTokens) ==> 
    (fresh(token) && token.matches(fingerprint, clearance, true) && issuedTokens == old(issuedTokens) + {fingerprint})
  modifies this`issuedTokens
  {
    if (fingerprint in issuedTokens) {
      token := null;
    } else {
      issuedTokens := issuedTokens + {fingerprint};
      token := new Token(fingerprint, clearance);
    }
  }
}

datatype ResourceState = Open | Closed

class IdStation {
  var securityLevel : int;
  var alarm : bool
  var state : ResourceState

  constructor(securityLevel : int)
  requires securityLevel in {0, 1, 2}
  ensures this.securityLevel == securityLevel && alarm == false && state == Closed
  {
    this.securityLevel := securityLevel;
    alarm := false;
    state := Closed;
  }

  predicate isOKToOpen(token : Token, fingerprint : int)
  reads token, this`securityLevel
  {
    token.isValidFingerprintPredicate(fingerprint) && token.getClearanceFunction() >= securityLevel
  }

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

  method close()
  ensures state == Closed
  modifies this`state
  {
    state := Closed;
  }

  method isOpen() returns (result : bool)
  ensures result == (state == Open)
  {
    result := (state == Open);
  }

  method isClosed() returns (result : bool)
  ensures result == (state == Closed)
  {
    result := (state == Closed);
  }

  method isAlarm() returns (result : bool)
  ensures result == alarm
  {
    result := alarm;
  }

}

method testToken() {
  // Should be a valid fingerprint when given fingerprint that matches token
  var token := new Token(0, 0);
  var isValidFingerprint := token.isValidFingerprint(0);
  assert (isValidFingerprint);
  var isValidToken := token.isValidToken();
  assert (isValidToken);
  
  // Should be an invalid fingerprint when given fingerprint that does not match token
  isValidFingerprint := token.isValidFingerprint(1);
  assert (!isValidFingerprint);
  isValidToken := token.isValidToken();
  assert (!isValidToken);

  // Should return level 0 when created with level 0
  var clearance := token.getClearance();
  assert (clearance == 0);
}

method testEnrollementStation() {
  var enrollementStation := new EnrollementStation();

  // Should return fresh token when fingerprint is not enrolled
  var tokenOne := enrollementStation.getToken(0, 0);
  assert (fresh(tokenOne));
  
  // Should return null token when fingerprint is enrolled
  var tokenTwo := enrollementStation.getToken(0, 0);
  assert (tokenTwo == null);

  // Should return fresh token when new fingerprint is enrolled
  var tokenThree := enrollementStation.getToken(1, 0);
  assert (tokenThree != null);
}

method testIDStation() {
  var idStation := new IdStation(1);

  // Should open when given a token, matching fingerprint, and same security level
  var token := new Token(0, 1);
  idStation.open(token, 0);
  var isOpen := idStation.isOpen();
  var isAlarm := idStation.isAlarm();
  assert (isOpen && !isAlarm);

  // Should close when close is called
  idStation.close();
  var isClosed := idStation.isClosed();
  isAlarm := idStation.isAlarm();
  assert (isClosed && !isAlarm);

  // Should not open when given token, matching fingerprint, and lower security level
  token := new Token(0, 0);
  idStation.open(token, 0);
  isClosed := idStation.isClosed();
  isAlarm := idStation.isAlarm();
  assert (isClosed && !isAlarm);

  // Should not open and alarm when given token and a mismatching fingerprint
  token := new Token(0, 1);
  idStation.open(token, 1);
  isClosed := idStation.isClosed();
  isAlarm := idStation.isAlarm();
  assert (isClosed && isAlarm);
}

method testSystem() {
  var enrollementStation := new EnrollementStation();
  var idStation := new IdStation(1);

  // Should open when given issued token with matching fingerprint and security level
  var tokenOne := enrollementStation.getToken(0, 1);
  idStation.open(tokenOne, 0);
  var isOpen := idStation.isOpen();
  var isAlarm := idStation.isAlarm();
  assert (isOpen && !isAlarm);
  idStation.close();

  // Should not open when given issued token with matching fingerprint but lower security level
  var tokenTwo := enrollementStation.getToken(1, 0);
  assert (tokenTwo != null);
  isOpen := idStation.isOpen();
  isAlarm := idStation.isAlarm();
  idStation.close();

  // Should not open and sound alarm with givin token with mismatced fingerprint
  idStation.open(tokenTwo, 0);
  var isClosed := idStation.isClosed();
  isAlarm := idStation.isAlarm();
  assert (isAlarm && isClosed); 
}