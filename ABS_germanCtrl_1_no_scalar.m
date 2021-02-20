const
    NODE_NUM : 2;
    DATA_NUM : 2;

type
     NODE : 1..NODE_NUM;
     DATA : 1..DATA_NUM;
     
     ABS_NODE : union {NODE, enum{Other}};

     CACHE_STATE : enum{I, S, E};
     CACHE : record State : CACHE_STATE;  end;
     
     MSG_CMD : enum{Empty, ReqS, ReqE, Inv, InvAck, GntS, GntE};
     MSG : record Cmd : MSG_CMD;   end;

var
    Cache: array [NODE] of CACHE;
    Chan1: array [NODE] of MSG;
    Chan2: array [NODE] of MSG;
    Chan3: array [NODE] of MSG;
    ShrSet: array [NODE] of boolean;
    InvSet: array [NODE] of boolean;
    ExGntd: boolean;
    CurCmd: MSG_CMD;
    CurPtr: ABS_NODE;
     
    

ruleset d: DATA do startstate "Init"
 for i: NODE do
   Chan1[i].Cmd := Empty;
   Chan2[i].Cmd := Empty; 
   Chan3[i].Cmd := Empty;   
      
   Cache[i].State := I;
    
   ShrSet[i] := false;
   InvSet[i] := false;
  end;
  CurCmd := Empty;
  ExGntd := false;
   
endstartstate; endruleset;

ruleset j: NODE do
 rule "SendReqS"
      Cache[j].State = I & Chan1[j].Cmd = Empty ==> 
        begin Chan1[j].Cmd := ReqS;
endrule; endruleset;

ruleset i: NODE do
 rule "SendReqEI"
      (Cache[i].State = I) & Chan1[i].Cmd = Empty ==> 
        begin Chan1[i].Cmd := ReqE;
endrule; endruleset;

ruleset i: NODE do
 rule "SendReqES"
      (Cache[i].State = S) & Chan1[i].Cmd = Empty ==> 
        begin Chan1[i].Cmd := ReqE;
endrule; endruleset;

ruleset i: NODE do
 rule "RecvReq"
       CurCmd = Empty & Chan1[i].Cmd != Empty ==>
        begin CurCmd := Chan1[i].Cmd; 
              Chan1[i].Cmd := Empty;
              CurPtr := i;
              for j: NODE do
               InvSet[j] := ShrSet[j];
              endfor;
endrule; endruleset;
  
ruleset i: NODE do
 rule "SendInvE"
      (CurCmd = ReqE)
      & InvSet[i] & Chan2[i].Cmd = Empty ==>
       begin
        Chan2[i].Cmd := Inv;
        InvSet[i] := false;
endrule; endruleset;
  
ruleset i: NODE do
 rule "SendInvS"
      (CurCmd = ReqS & ExGntd)
      & InvSet[i] & Chan2[i].Cmd = Empty ==>
       begin
        Chan2[i].Cmd := Inv;
        InvSet[i] := false;
endrule; endruleset;
 
ruleset i: NODE do
 rule "SendInvAck"
      Chan2[i].Cmd = Inv & Chan3[i].Cmd = Empty ==>
      begin
       Chan2[i].Cmd := Empty;
       Chan3[i].Cmd := InvAck;
        
       Cache[i].State := I;
endrule; endruleset;

ruleset i: NODE do
 rule "RecvInvAck1"
      CurCmd != Empty & Chan3[i].Cmd = InvAck &(ExGntd = true)==>
      begin 
       ShrSet[i] := false;
       
       ExGntd := false; 
      
       Chan3[i].Cmd := Empty;
endrule; endruleset;

ruleset i: NODE do
 rule "RecvInvAck2"
      CurCmd != Empty & Chan3[i].Cmd = InvAck&(ExGntd = false) ==>
      begin 
       ShrSet[i] := false;
        
       Chan3[i].Cmd := Empty;
endrule; endruleset;

ruleset i: NODE do
 rule "SendGntS"
      CurCmd = ReqS & CurPtr = i
      & !ExGntd & Chan2[i].Cmd = Empty ==>
      begin
       ShrSet[i] := true;
       CurCmd := Empty;
       Chan2[i].Cmd := GntS;
       
endrule; endruleset;

ruleset i: NODE do
 rule "SendGntE"
      CurCmd = ReqE & CurPtr = i & !ExGntd 
      & forall j: NODE do ShrSet[j] = false endforall
      & Chan2[i].Cmd = Empty ==>
      begin
       ShrSet[i] := true;
       CurCmd := Empty;
       ExGntd := true;
       Chan2[i].Cmd := GntE;
        
endrule; endruleset;

ruleset i: NODE do
 rule "RecvGntS"
      Chan2[i].Cmd = GntS ==>
      begin
       Cache[i].State := S;
       Chan2[i].Cmd := Empty;
        
endrule; endruleset;

ruleset i: NODE do
 rule "RecvGntE"
      Chan2[i].Cmd = GntE ==>
      begin
       Cache[i].State := E;
       Chan2[i].Cmd := Empty;
       
endrule; endruleset;

 
ruleset i: NODE; j: NODE do
invariant "CntrlProp"
      (Cache[i].State = E -> Cache[j].State != E);
endruleset;

 


-- No abstract rule for rule SendReqS



-- No abstract rule for rule SendReqEI



-- No abstract rule for rule SendReqES


rule "n_ABS_RecvReq_NODE_1"

	CurCmd = Empty
==>
begin
	CurPtr := Other;
	for NODE_2 : NODE do
		InvSet[NODE_2] := ShrSet[NODE_2] ;
		;
	endfor;
endrule;

-- No abstract rule for rule SendInvE



-- No abstract rule for rule SendInvS



-- No abstract rule for rule SendInvAck


rule "n_ABS_RecvInvAck1_NODE_1"

	CurCmd != Empty &
	(ExGntd = true)
==>
begin
	ExGntd := false;
endrule;

-- No abstract rule for rule RecvInvAck2


rule "n_ABS_SendGntS_NODE_1"

	CurCmd = ReqS &
	CurPtr = Other &
	!ExGntd
==>
begin
	CurCmd := Empty;
endrule;
rule "n_ABS_SendGntE_NODE_1"

	CurCmd = ReqE &
	CurPtr = Other &
	!ExGntd
	& forall NODE_2 : NODE do
			ShrSet[NODE_2] = false
	end
==>
begin
	CurCmd := Empty ;
	ExGntd := true;
endrule;

-- No abstract rule for rule RecvGntS



-- No abstract rule for rule RecvGntE



ruleset i : NODE ; j : NODE do
Invariant "rule_1"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_2"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_3"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_4"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_5"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_6"
	(Chan2[i].Cmd = GntS -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_7"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_8"
	(Chan2[i].Cmd = GntE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_9"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_10"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_11"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_12"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_13"
		(i != j) ->	(Chan2[i].Cmd = GntE -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_14"
		(i != j) ->	(Chan2[i].Cmd = GntE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_15"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntS);
endruleset;
