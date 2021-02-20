const
    NODE_NUM : 2;
    DATA_NUM : 2;

type
     NODE : scalarset(NODE_NUM);
     DATA : scalarset(DATA_NUM);
     
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

 


ruleset i : NODE ; j : NODE do
Invariant "rule_671"
		(i != j) ->	(Chan1[j].Cmd != Empty -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_719"
		(i != j) ->	(Chan1[i].Cmd != Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_484"
	(Chan2[i].Cmd = GntS -> ShrSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_360"
	(Cache[j].State != S -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_770"
		(i != j) ->	(Chan3[j].Cmd = Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_251"
	(Chan2[i].Cmd != GntE -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_668"
	(CurCmd = ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_782"
	(CurCmd != ReqS -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_811"
		(i != j) ->	(Chan2[i].Cmd != Inv -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_167"
	(CurCmd = ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_67"
		(i != j) ->	(Chan2[j].Cmd = Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_827"
		(i != j) ->	(Chan3[i].Cmd = Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_651"
	(Chan2[i].Cmd = Empty -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_26"
	(Chan3[j].Cmd != InvAck -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_674"
	(Chan1[i].Cmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_407"
	(ExGntd = true -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_328"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_540"
	(ShrSet[j] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_49"
		(i != j) ->	(Chan2[j].Cmd != GntE -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_925"
		(i != j) ->	(CurCmd = ReqE & Chan1[j].Cmd = ReqE -> Chan1[i].Cmd != ReqS);
endruleset;
Invariant "rule_623"
	(ExGntd = true -> CurCmd != ReqE);


ruleset i : NODE ; j : NODE do
Invariant "rule_557"
		(i != j) ->	(Chan1[i].Cmd != Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_537"
	(Cache[i].State = I -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_796"
	(Chan1[i].Cmd != ReqS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_736"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_583"
	(ExGntd = false -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_713"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_84"
		(i != j) ->	(InvSet[j] = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_191"
	(Cache[i].State != E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_140"
	(ShrSet[i] = true -> CurCmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_900"
		(i != j) ->	(CurCmd = ReqE & Chan1[i].Cmd != Empty -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_216"
	(CurCmd != ReqS -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_805"
		(i != j) ->	(Chan2[i].Cmd != Inv -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_785"
	(CurCmd != Empty -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_163"
	(Chan2[j].Cmd = Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_917"
		(i != j) ->	(CurCmd = ReqS & Chan1[j].Cmd = ReqS -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_752"
	(ExGntd = true -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_469"
		(i != j) ->	(Chan1[j].Cmd != ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_695"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_685"
		(i != j) ->	(Chan1[j].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_764"
	(Cache[j].State != E -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_834"
	(CurCmd != ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_640"
		(i != j) ->	(Chan1[i].Cmd != Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_138"
	(Chan1[j].Cmd = ReqE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_240"
		(i != j) ->	(ShrSet[i] = false -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_588"
		(i != j) ->	(Chan3[j].Cmd != InvAck -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_971"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[i].Cmd != Empty -> CurCmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_391"
	(Chan2[i].Cmd = GntE -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_933"
	(Chan2[i].Cmd != GntS & Chan2[i].Cmd != Empty -> ExGntd = true);
endruleset;


ruleset j : NODE do
Invariant "rule_778"
	(Chan1[j].Cmd = ReqS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_415"
	(CurCmd != Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_599"
		(i != j) ->	(Chan1[j].Cmd != Empty -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_374"
	(Chan2[j].Cmd != GntE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_378"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_27"
	(ExGntd = true -> Chan2[i].Cmd != Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_295"
	(ExGntd = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_611"
	(Cache[j].State = I -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_638"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_120"
		(i != j) ->	(Chan1[j].Cmd != ReqE -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_968"
		(i != j) ->	(CurCmd = ReqE & Chan1[i].Cmd = ReqE -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_712"
	(Chan2[i].Cmd = GntS -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_720"
	(Chan2[i].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_193"
	(Chan1[j].Cmd != ReqE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_284"
	(CurCmd != ReqS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_368"
	(Cache[j].State != E -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_656"
		(i != j) ->	(Chan2[i].Cmd != GntE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_701"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_473"
	(Chan1[j].Cmd = Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_339"
	(Cache[j].State = I -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_288"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_976"
		(i != j) ->	(Chan1[i].Cmd != Empty & CurCmd != Empty -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_650"
	(Chan1[i].Cmd = Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_726"
	(CurCmd != ReqE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_326"
		(i != j) ->	(Chan1[j].Cmd != Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_492"
		(i != j) ->	(ShrSet[i] = true -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_476"
		(i != j) ->	(Chan1[j].Cmd != ReqE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_62"
		(i != j) ->	(Chan1[i].Cmd != Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_318"
	(InvSet[i] = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_10"
	(Chan1[i].Cmd != ReqE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_561"
		(i != j) ->	(Chan2[j].Cmd != Inv -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_277"
	(ExGntd = false -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_509"
	(Chan1[j].Cmd = ReqS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_3"
	(ExGntd = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_77"
	(ExGntd = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_463"
		(i != j) ->	(InvSet[i] = false -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_686"
		(i != j) ->	(Cache[i].State != S -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_250"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_454"
	(Chan3[j].Cmd = Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_507"
	(Chan1[j].Cmd = ReqS -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_185"
		(i != j) ->	(Cache[i].State = I -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_619"
	(Chan3[j].Cmd != InvAck -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_78"
	(CurCmd = Empty -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_734"
	(Chan3[j].Cmd != InvAck -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_375"
		(i != j) ->	(Cache[j].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_453"
	(Chan2[j].Cmd = Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_197"
		(i != j) ->	(Chan2[i].Cmd = Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_758"
	(Chan1[j].Cmd != Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_432"
	(InvSet[i] = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_721"
	(Chan1[j].Cmd != ReqE -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_934"
		(i != j) ->	(CurCmd = ReqE & Chan1[i].Cmd = ReqS -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_212"
		(i != j) ->	(Chan1[j].Cmd = Empty -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_704"
	(Chan1[j].Cmd != ReqE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_493"
		(i != j) ->	(Chan2[i].Cmd != GntS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_733"
	(ExGntd = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_806"
		(i != j) ->	(Cache[i].State = I -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_362"
	(Chan1[i].Cmd != Empty -> Chan2[i].Cmd != GntS);
endruleset;
Invariant "rule_456"
	(CurCmd != Empty -> ExGntd = false);


ruleset i : NODE ; j : NODE do
Invariant "rule_221"
		(i != j) ->	(ShrSet[i] = true -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_427"
	(Chan1[i].Cmd = ReqS -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_112"
	(Chan2[i].Cmd != Empty -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_234"
		(i != j) ->	(ShrSet[i] = true -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_354"
	(CurCmd = Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_42"
		(i != j) ->	(Chan1[j].Cmd = Empty -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_131"
	(Chan2[j].Cmd != GntE -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_304"
		(i != j) ->	(Cache[i].State != E -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_2"
	(CurCmd != ReqS -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_594"
		(i != j) ->	(InvSet[i] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_832"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_377"
	(Chan1[j].Cmd != ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_314"
	(CurCmd != ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_178"
		(i != j) ->	(Chan1[j].Cmd = Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_310"
		(i != j) ->	(Chan3[i].Cmd = Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_296"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_309"
		(i != j) ->	(Chan2[j].Cmd != Inv -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1"
		(i != j) ->	(Chan1[j].Cmd != ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_32"
	(CurCmd = ReqE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_137"
	(Chan2[i].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_728"
		(i != j) ->	(Chan1[i].Cmd = Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_307"
		(i != j) ->	(Chan1[i].Cmd = Empty -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_247"
	(CurCmd != ReqS -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_225"
	(Cache[j].State != S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_257"
	(CurCmd != Empty -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_14"
		(i != j) ->	(Chan3[i].Cmd = Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_894"
		(i != j) ->	(CurCmd = ReqE & Chan1[j].Cmd != Empty -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_429"
		(i != j) ->	(Cache[i].State != E -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_170"
	(Chan3[j].Cmd != InvAck -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_581"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_745"
		(i != j) ->	(Cache[j].State != S -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_831"
		(i != j) ->	(Chan1[i].Cmd = Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_762"
		(i != j) ->	(Cache[j].State != E -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_156"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_624"
	(CurCmd != Empty -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_442"
	(Cache[j].State = I -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_287"
		(i != j) ->	(ShrSet[i] = false -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_184"
	(Chan1[j].Cmd != Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_912"
		(i != j) ->	(Chan1[i].Cmd != ReqS & Chan1[i].Cmd != Empty -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_420"
	(CurCmd = ReqS -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_767"
		(i != j) ->	(Chan2[i].Cmd != Inv -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_807"
		(i != j) ->	(Chan2[j].Cmd = Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_96"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_107"
	(Chan2[j].Cmd != GntS -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_457"
		(i != j) ->	(Chan3[j].Cmd != InvAck -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_115"
		(i != j) ->	(Cache[i].State != S -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_414"
	(Chan1[i].Cmd = ReqE -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_237"
		(i != j) ->	(ShrSet[i] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_486"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_400"
	(Chan2[i].Cmd = GntS -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_896"
	(Chan2[i].Cmd != GntS & Chan2[i].Cmd != GntE -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_593"
	(Chan1[j].Cmd = ReqE -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_731"
	(Chan3[j].Cmd != InvAck -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_751"
	(Chan1[j].Cmd = ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_340"
	(Chan1[j].Cmd != ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_89"
		(i != j) ->	(Chan2[j].Cmd != GntS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_904"
		(i != j) ->	(CurCmd = Empty & Chan1[j].Cmd != ReqE -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_70"
	(Cache[i].State != E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_83"
		(i != j) ->	(Chan3[i].Cmd = Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_772"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_967"
		(i != j) ->	(Chan1[i].Cmd = ReqE & Chan1[j].Cmd = ReqE -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_224"
	(Chan2[j].Cmd != Inv -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_531"
		(i != j) ->	(ShrSet[i] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_129"
		(i != j) ->	(ShrSet[i] = true -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_371"
	(Cache[i].State = I -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_315"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_210"
		(i != j) ->	(Chan2[j].Cmd != GntS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_418"
		(i != j) ->	(Cache[i].State != E -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_710"
	(CurCmd != ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_61"
	(CurCmd = ReqS -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_818"
	(Chan1[i].Cmd != ReqE -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_783"
	(Chan1[j].Cmd = Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_279"
		(i != j) ->	(Cache[j].State != S -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_618"
	(Chan2[j].Cmd = Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_487"
	(Chan2[i].Cmd != Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_756"
		(i != j) ->	(Chan2[i].Cmd != GntS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_38"
	(Chan3[j].Cmd != InvAck -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_856"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_6"
	(Cache[j].State != E -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_481"
	(ExGntd = true -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_395"
		(i != j) ->	(Chan2[i].Cmd = Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_384"
		(i != j) ->	(Cache[j].State != E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_383"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_641"
	(InvSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_346"
		(i != j) ->	(Chan3[i].Cmd = Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_803"
	(CurCmd = Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_264"
	(ShrSet[i] = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_649"
		(i != j) ->	(ShrSet[j] = false -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_567"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_817"
	(CurCmd != ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_949"
		(i != j) ->	(Chan1[i].Cmd != Empty & CurCmd != Empty -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_347"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_784"
	(CurCmd != Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_176"
		(i != j) ->	(Chan3[i].Cmd = Empty -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_8"
	(Chan1[j].Cmd != ReqS -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_81"
		(i != j) ->	(Cache[i].State != S -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_679"
		(i != j) ->	(Chan2[j].Cmd != GntS -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_547"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_31"
		(i != j) ->	(Cache[i].State != S -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_289"
	(Chan1[j].Cmd = ReqE -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_551"
	(CurCmd != Empty -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_465"
	(ShrSet[i] = true -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_94"
	(CurCmd != ReqE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_291"
		(i != j) ->	(Chan2[i].Cmd = Empty -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_450"
		(i != j) ->	(Chan2[i].Cmd != GntS -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_219"
		(i != j) ->	(Chan1[i].Cmd = Empty -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_397"
	(Chan2[j].Cmd != Inv -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_338"
	(Chan3[j].Cmd != InvAck -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_706"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_962"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan1[j].Cmd != Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_57"
	(ExGntd = true -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_781"
	(Chan2[j].Cmd != GntE -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_578"
	(CurCmd != ReqE -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_750"
	(Chan1[j].Cmd != Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_503"
	(Chan2[i].Cmd = GntE -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_169"
	(Chan1[i].Cmd = ReqS -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_68"
		(i != j) ->	(ShrSet[i] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_959"
		(i != j) ->	(CurCmd = Empty & Chan1[j].Cmd = Empty -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_768"
		(i != j) ->	(Chan1[i].Cmd != Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_214"
		(i != j) ->	(Cache[i].State = I -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_399"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_155"
	(Chan2[i].Cmd = GntE -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_462"
	(InvSet[i] = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_249"
	(CurCmd = ReqE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_105"
	(InvSet[j] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_125"
	(CurCmd = ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_775"
	(Chan1[i].Cmd = Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_829"
		(i != j) ->	(Chan2[i].Cmd != GntE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_259"
		(i != j) ->	(InvSet[i] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_359"
	(InvSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_789"
	(Chan2[i].Cmd != GntE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_46"
		(i != j) ->	(InvSet[i] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_128"
	(CurCmd = ReqS -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_876"
		(i != j) ->	(Cache[j].State != E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_716"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_468"
		(i != j) ->	(Chan2[i].Cmd = GntE -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_69"
	(Chan2[i].Cmd = GntS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_688"
	(Chan1[i].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_771"
	(ExGntd = true -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_886"
	(Chan1[i].Cmd = ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_104"
		(i != j) ->	(Chan2[i].Cmd = Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_844"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_449"
	(CurCmd = ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_920"
		(i != j) ->	(Chan1[i].Cmd = ReqS & Chan1[j].Cmd = ReqE -> CurCmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_470"
	(CurCmd = ReqE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_86"
		(i != j) ->	(ShrSet[i] = true -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_430"
		(i != j) ->	(InvSet[j] = false -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_954"
		(i != j) ->	(Chan1[i].Cmd != Empty & Chan1[j].Cmd = ReqS -> CurCmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_334"
		(i != j) ->	(ShrSet[j] = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_444"
	(ShrSet[i] = true -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_230"
		(i != j) ->	(ShrSet[j] = false -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_408"
	(Cache[j].State != S -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_435"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_386"
		(i != j) ->	(ShrSet[j] = false -> InvSet[i] = false);
endruleset;
Invariant "rule_613"
	(CurCmd = ReqS -> ExGntd = false);


ruleset i : NODE ; j : NODE do
Invariant "rule_617"
		(i != j) ->	(Chan2[j].Cmd != GntE -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_99"
	(ExGntd = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_569"
	(CurCmd = ReqS -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_627"
	(ShrSet[i] = false -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_884"
		(i != j) ->	(Chan1[j].Cmd != ReqS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_282"
		(i != j) ->	(Chan1[i].Cmd = Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_689"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_233"
	(ShrSet[i] = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_606"
	(CurCmd != ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_605"
		(i != j) ->	(Chan1[j].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_975"
		(i != j) ->	(CurCmd != Empty & Chan1[j].Cmd = ReqE -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_66"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_924"
		(i != j) ->	(Chan1[i].Cmd = ReqE & CurCmd != Empty -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_880"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_222"
		(i != j) ->	(Chan1[j].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_252"
	(Cache[i].State != S -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_634"
	(ShrSet[i] = true -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_428"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_963"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[i].Cmd = ReqE -> CurCmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_923"
		(i != j) ->	(Chan1[i].Cmd = ReqE & Chan1[j].Cmd != ReqE -> CurCmd != Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_23"
	(CurCmd != ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_20"
	(CurCmd != ReqS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_159"
	(CurCmd = ReqE -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_353"
	(Chan1[i].Cmd = ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_676"
		(i != j) ->	(Chan2[i].Cmd != GntS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_51"
	(Chan2[i].Cmd != GntS -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_21"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_960"
		(i != j) ->	(CurCmd = ReqE & Chan1[i].Cmd = ReqS -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_903"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[i].Cmd = ReqE -> CurCmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_168"
		(i != j) ->	(Chan1[j].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_684"
	(Chan2[i].Cmd != GntS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_763"
	(Chan3[j].Cmd = Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_189"
	(ShrSet[i] = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_12"
	(CurCmd = Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_337"
	(Chan1[i].Cmd = Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_950"
		(i != j) ->	(CurCmd = ReqS & Chan1[j].Cmd != Empty -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_519"
		(i != j) ->	(Chan1[j].Cmd != Empty -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_244"
	(CurCmd != Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_43"
	(Chan1[i].Cmd = Empty -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_323"
	(Chan2[j].Cmd != GntS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_150"
		(i != j) ->	(Chan1[i].Cmd != Empty -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_255"
	(CurCmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_532"
	(Chan1[j].Cmd = ReqS -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_715"
	(Chan1[i].Cmd != ReqS -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_536"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_29"
	(ExGntd = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_151"
	(Chan1[i].Cmd = ReqS -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_867"
	(Cache[j].State = I -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_367"
	(Chan2[j].Cmd != GntS -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_299"
	(ExGntd = true -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_839"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_601"
	(Chan2[i].Cmd != Empty -> CurCmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_417"
		(i != j) ->	(Chan1[j].Cmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_440"
		(i != j) ->	(InvSet[i] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_174"
	(ExGntd = true -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_816"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_828"
	(Chan2[i].Cmd = GntS -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_626"
		(i != j) ->	(Chan2[i].Cmd != Inv -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_478"
	(ExGntd = true -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_308"
	(Chan2[i].Cmd = GntS -> Chan1[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_582"
	(CurCmd != ReqE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_241"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_773"
		(i != j) ->	(InvSet[j] = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_106"
	(Chan2[j].Cmd != Inv -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_93"
	(ExGntd = true -> Chan2[i].Cmd = GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_655"
	(Chan1[j].Cmd != Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_659"
	(Chan1[i].Cmd = ReqS -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_891"
		(i != j) ->	(CurCmd != Empty & Chan1[j].Cmd = ReqE -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_732"
	(Chan2[j].Cmd != GntE -> Chan3[j].Cmd != InvAck);
endruleset;
Invariant "rule_447"
	(CurCmd = ReqE -> ExGntd = false);


ruleset j : NODE do
Invariant "rule_28"
	(CurCmd = ReqS -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_55"
	(CurCmd = ReqS -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_182"
	(Chan1[j].Cmd != Empty -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_36"
	(CurCmd = Empty -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_953"
		(i != j) ->	(CurCmd = Empty & Chan1[j].Cmd = Empty -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_761"
		(i != j) ->	(Cache[i].State = I -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_765"
		(i != j) ->	(Chan1[i].Cmd != Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_500"
		(i != j) ->	(Chan2[i].Cmd != Inv -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_877"
		(i != j) ->	(Chan2[i].Cmd = Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_930"
		(i != j) ->	(CurCmd = ReqS & Chan1[j].Cmd = ReqE -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_628"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_558"
	(Cache[j].State != S -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_394"
	(Chan2[i].Cmd != Inv -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_425"
		(i != j) ->	(ShrSet[i] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_660"
	(CurCmd = ReqS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_777"
	(Chan1[i].Cmd != ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_144"
	(Chan2[j].Cmd != GntS -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_37"
	(ExGntd = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_434"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_209"
		(i != j) ->	(ShrSet[j] = false -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_298"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_181"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_272"
		(i != j) ->	(InvSet[j] = false -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_95"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_544"
		(i != j) ->	(Chan2[j].Cmd != GntE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_609"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_231"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_495"
		(i != j) ->	(Chan2[i].Cmd != GntE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_98"
	(Chan2[i].Cmd != Empty -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_204"
		(i != j) ->	(Chan2[j].Cmd != GntE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_73"
		(i != j) ->	(Chan2[j].Cmd != GntS -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_130"
	(InvSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_748"
	(Chan1[j].Cmd != ReqS -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_108"
	(Cache[j].State != S -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_570"
	(ExGntd = true -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_524"
	(CurCmd != Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_92"
	(Chan2[i].Cmd = GntE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_851"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_194"
		(i != j) ->	(Chan1[j].Cmd != Empty -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_883"
	(Chan1[j].Cmd = Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_743"
	(CurCmd != Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_60"
		(i != j) ->	(ShrSet[i] = true -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_898"
		(i != j) ->	(CurCmd = ReqE & Chan1[j].Cmd != Empty -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_667"
	(Chan1[i].Cmd = ReqE -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_645"
		(i != j) ->	(Cache[i].State != S -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_657"
	(CurCmd = ReqE -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_625"
		(i != j) ->	(InvSet[j] = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_614"
	(InvSet[i] = false -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_631"
	(Chan1[j].Cmd != ReqE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_830"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_127"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_379"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_610"
	(Chan2[j].Cmd = Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_860"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_740"
		(i != j) ->	(Chan2[i].Cmd = GntS -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_152"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_571"
		(i != j) ->	(Chan1[i].Cmd = Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_666"
		(i != j) ->	(Chan2[i].Cmd != GntE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_698"
	(CurCmd = ReqE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_560"
		(i != j) ->	(Cache[i].State != E -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_85"
		(i != j) ->	(Chan3[i].Cmd = Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_58"
	(CurCmd = ReqE -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_325"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_333"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_188"
	(CurCmd != ReqS -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_352"
	(Cache[i].State != S -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_322"
	(Chan2[i].Cmd = Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_965"
		(i != j) ->	(CurCmd = ReqE & Chan1[i].Cmd != Empty -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_944"
		(i != j) ->	(Chan1[i].Cmd = ReqS & Chan1[j].Cmd = ReqE -> CurCmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_505"
		(i != j) ->	(Chan2[i].Cmd = Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_280"
	(Chan3[j].Cmd = Empty -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_970"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd != Empty -> Chan1[j].Cmd != Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_795"
	(Chan1[j].Cmd = ReqE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_401"
	(Chan1[i].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_899"
		(i != j) ->	(CurCmd = Empty & Chan1[j].Cmd = Empty -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_445"
	(Chan1[j].Cmd = Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_697"
		(i != j) ->	(Chan1[i].Cmd = Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_842"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_874"
		(i != j) ->	(Chan1[i].Cmd = Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_580"
		(i != j) ->	(Chan3[i].Cmd = Empty -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_39"
	(ShrSet[j] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_373"
	(ShrSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_313"
	(Cache[i].State = I -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_145"
	(ShrSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_472"
	(Chan2[i].Cmd != Empty -> CurCmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_648"
		(i != j) ->	(Cache[i].State != S -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_819"
	(Chan3[j].Cmd != InvAck -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_966"
		(i != j) ->	(CurCmd = ReqE & Chan1[j].Cmd = ReqS -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_749"
	(Chan2[i].Cmd != GntS -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_776"
	(Chan1[i].Cmd != Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_80"
		(i != j) ->	(Chan3[j].Cmd != InvAck -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_682"
	(ShrSet[j] = false -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_535"
		(i != j) ->	(Chan3[j].Cmd != InvAck -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_665"
		(i != j) ->	(Cache[j].State != S -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_939"
	(ExGntd = false & ShrSet[i] = true -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_136"
	(CurCmd != ReqE -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_355"
	(ShrSet[i] = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_637"
	(Chan1[j].Cmd != ReqS -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_88"
	(Chan2[i].Cmd = GntE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_890"
		(i != j) ->	(CurCmd != Empty & Chan1[j].Cmd = ReqE -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_207"
	(Chan2[i].Cmd = GntS -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_341"
		(i != j) ->	(Chan1[j].Cmd != ReqE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_595"
		(i != j) ->	(Chan2[j].Cmd != Inv -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_286"
		(i != j) ->	(ShrSet[i] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_727"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_273"
		(i != j) ->	(InvSet[i] = false -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_926"
		(i != j) ->	(Chan1[i].Cmd = ReqE & Chan1[j].Cmd = ReqE -> CurCmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_474"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_793"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_940"
		(i != j) ->	(Chan1[i].Cmd != Empty & Chan1[j].Cmd = ReqE -> CurCmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_211"
		(i != j) ->	(Chan2[i].Cmd != Inv -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_265"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_218"
	(InvSet[i] = false -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_759"
		(i != j) ->	(Chan1[i].Cmd != Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_404"
		(i != j) ->	(Chan1[j].Cmd != Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_708"
	(Chan1[i].Cmd = ReqS -> ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_258"
	(ShrSet[i] = false -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_699"
	(ExGntd = true -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_677"
	(CurCmd != Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_797"
		(i != j) ->	(Chan2[i].Cmd != GntS -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_510"
	(Chan1[i].Cmd != ReqS -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_300"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_870"
	(Chan3[i].Cmd != InvAck -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_48"
		(i != j) ->	(InvSet[i] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_54"
	(Chan2[i].Cmd = GntE -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_34"
	(Chan2[i].Cmd = Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_792"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_409"
	(ShrSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_529"
	(Chan3[i].Cmd != InvAck -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_545"
	(ExGntd = true -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_577"
	(ExGntd = true -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_705"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_647"
		(i != j) ->	(Chan2[j].Cmd != Inv -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_448"
	(Chan2[i].Cmd != Empty -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_780"
	(Cache[j].State != E -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_587"
		(i != j) ->	(Cache[i].State = I -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_403"
	(CurCmd = ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_215"
		(i != j) ->	(Chan2[j].Cmd != GntS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_717"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_533"
	(ExGntd = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_186"
		(i != j) ->	(InvSet[j] = false -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_514"
	(Chan1[j].Cmd != Empty -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_893"
		(i != j) ->	(Chan1[j].Cmd != Empty & CurCmd != Empty -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_396"
	(Chan1[i].Cmd = ReqS -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_388"
	(CurCmd != Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_746"
	(Chan2[i].Cmd != Empty -> Chan1[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_629"
	(Chan3[j].Cmd = Empty -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_498"
	(CurCmd = Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_809"
	(ExGntd = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_664"
		(i != j) ->	(Cache[i].State = I -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_162"
		(i != j) ->	(Chan2[i].Cmd != Inv -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_892"
		(i != j) ->	(CurCmd = ReqS & Chan1[i].Cmd != Empty -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_369"
	(ExGntd = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_11"
	(CurCmd != ReqE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_203"
		(i != j) ->	(Cache[i].State = I -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_630"
	(Cache[j].State != S -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_855"
	(CurCmd = ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_517"
		(i != j) ->	(Cache[j].State != E -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_381"
		(i != j) ->	(Chan2[i].Cmd != GntS -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_592"
	(Chan2[i].Cmd != Inv -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_118"
		(i != j) ->	(Cache[i].State != E -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_122"
		(i != j) ->	(Chan3[j].Cmd != InvAck -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_635"
		(i != j) ->	(Cache[i].State = I -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_584"
		(i != j) ->	(ShrSet[i] = true -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_459"
	(CurCmd = ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_632"
	(CurCmd = ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_522"
	(ShrSet[j] = false -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_438"
	(Chan1[j].Cmd != ReqS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_849"
	(Chan2[i].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_488"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_433"
	(Chan2[i].Cmd != Inv -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_573"
	(Chan2[i].Cmd = GntE -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_709"
		(i != j) ->	(Chan1[j].Cmd != Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_19"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_835"
	(Chan1[j].Cmd != Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_223"
		(i != j) ->	(ShrSet[i] = true -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_141"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_511"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_799"
		(i != j) ->	(Chan2[i].Cmd != Empty -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_208"
		(i != j) ->	(Cache[i].State != E -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_422"
	(Chan1[j].Cmd = ReqE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_553"
		(i != j) ->	(Chan2[i].Cmd = Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_412"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_398"
	(Cache[j].State != E -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_852"
	(Chan1[i].Cmd = ReqS -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_958"
		(i != j) ->	(Chan1[j].Cmd != Empty & CurCmd != Empty -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_301"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_356"
	(InvSet[j] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_653"
	(Chan3[j].Cmd = Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_97"
	(ShrSet[i] = true -> Chan2[i].Cmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_901"
		(i != j) ->	(CurCmd = ReqS & Chan1[j].Cmd != Empty -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_172"
	(Chan2[i].Cmd = Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_161"
		(i != j) ->	(Chan2[j].Cmd = Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_190"
	(Chan2[i].Cmd = GntS -> CurCmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_192"
	(Chan3[i].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_332"
	(Chan1[j].Cmd != ReqE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_928"
		(i != j) ->	(CurCmd = ReqS & Chan1[i].Cmd = ReqS -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_351"
	(InvSet[i] = false -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_278"
		(i != j) ->	(Cache[i].State != E -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_590"
		(i != j) ->	(ShrSet[i] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_515"
		(i != j) ->	(ShrSet[i] = true -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_157"
	(ShrSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_406"
	(CurCmd = ReqS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_345"
		(i != j) ->	(Chan2[j].Cmd = Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_50"
	(ExGntd = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_846"
	(Chan3[j].Cmd != InvAck -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_523"
	(CurCmd = ReqE -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_554"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_931"
		(i != j) ->	(CurCmd = ReqE & Chan1[j].Cmd = ReqS -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_675"
	(Chan2[i].Cmd = GntE -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_254"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_242"
	(Chan1[j].Cmd = ReqE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_833"
		(i != j) ->	(Cache[j].State != S -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_59"
	(Chan1[i].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_566"
	(ExGntd = false -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_103"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_439"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_246"
	(Chan1[i].Cmd = ReqE -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_24"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_297"
	(CurCmd != ReqS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_815"
		(i != j) ->	(Chan2[i].Cmd != GntS -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_389"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_504"
	(Chan1[j].Cmd != ReqE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_479"
	(Chan2[j].Cmd != Inv -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_845"
	(Chan1[j].Cmd = ReqE -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_766"
		(i != j) ->	(ShrSet[j] = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_317"
	(Chan2[i].Cmd = Empty -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_643"
	(Chan1[j].Cmd != ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_281"
	(ShrSet[j] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_419"
		(i != j) ->	(Chan2[j].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_410"
	(Chan1[i].Cmd != Empty -> ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_494"
	(Chan2[i].Cmd != GntS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_678"
		(i != j) ->	(InvSet[i] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_41"
		(i != j) ->	(ShrSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_501"
		(i != j) ->	(Chan2[i].Cmd != GntE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_5"
	(ShrSet[j] = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_687"
		(i != j) ->	(Chan2[j].Cmd != GntE -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_526"
		(i != j) ->	(Cache[i].State != S -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_602"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_349"
	(Chan2[i].Cmd = GntS -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_485"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_542"
	(Chan1[j].Cmd = ReqS -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_376"
		(i != j) ->	(Chan2[i].Cmd != Inv -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_854"
		(i != j) ->	(Cache[j].State = I -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_477"
	(Chan2[i].Cmd = GntE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_44"
	(ShrSet[i] = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_823"
		(i != j) ->	(Chan3[i].Cmd = Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_929"
		(i != j) ->	(CurCmd = ReqE & Chan1[j].Cmd = ReqE -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_40"
	(ExGntd = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_703"
	(Chan1[j].Cmd = ReqE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_166"
	(Chan2[i].Cmd = GntS -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_826"
		(i != j) ->	(Cache[j].State = I -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_82"
		(i != j) ->	(Chan3[j].Cmd = Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_135"
	(CurCmd != Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_729"
		(i != j) ->	(Chan1[i].Cmd != Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_722"
	(InvSet[j] = false -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_411"
	(Chan1[j].Cmd = Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_690"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_658"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_615"
	(Cache[i].State = I -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_342"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_260"
		(i != j) ->	(Chan2[j].Cmd = Empty -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_327"
	(CurCmd = Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_7"
	(CurCmd != ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_521"
	(InvSet[j] = false -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_18"
	(Chan2[j].Cmd != GntE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_426"
		(i != j) ->	(Chan1[j].Cmd != ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_607"
	(CurCmd = Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_229"
		(i != j) ->	(Cache[i].State = I -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_520"
	(CurCmd = Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_443"
	(Chan2[j].Cmd != GntE -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_227"
	(Chan1[j].Cmd = ReqS -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_464"
		(i != j) ->	(Cache[j].State = I -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_285"
	(Chan2[i].Cmd != Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_202"
	(Chan2[i].Cmd != GntE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_563"
	(CurCmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_910"
		(i != j) ->	(CurCmd = ReqS & Chan1[i].Cmd = ReqS -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_482"
		(i != j) ->	(ShrSet[i] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_329"
	(Chan1[j].Cmd = Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_942"
		(i != j) ->	(CurCmd = ReqS & Chan1[j].Cmd = ReqE -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_662"
		(i != j) ->	(Chan2[i].Cmd != Inv -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_546"
		(i != j) ->	(ShrSet[i] = true -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_808"
	(Chan1[j].Cmd = Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_913"
		(i != j) ->	(CurCmd = ReqS & Chan1[j].Cmd != Empty -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_871"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_725"
	(ExGntd = false -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_881"
	(Chan1[j].Cmd = Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_217"
	(Cache[i].State != E -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_555"
	(Chan1[i].Cmd != Empty -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_146"
	(ExGntd = false -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_575"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_53"
		(i != j) ->	(Chan2[i].Cmd != Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_306"
	(Chan1[i].Cmd != Empty -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_183"
	(Chan1[j].Cmd = Empty -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_753"
		(i != j) ->	(Cache[i].State != E -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_680"
		(i != j) ->	(Chan1[i].Cmd = Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_319"
	(Chan3[i].Cmd = Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_348"
		(i != j) ->	(Chan2[j].Cmd != Inv -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_357"
	(Chan2[j].Cmd = Empty -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_402"
	(CurCmd != ReqE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_516"
		(i != j) ->	(InvSet[i] = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_754"
		(i != j) ->	(Chan3[j].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_840"
		(i != j) ->	(Chan2[i].Cmd != GntS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_865"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_290"
	(CurCmd != ReqE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_869"
	(Cache[i].State != E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_604"
		(i != j) ->	(Chan2[i].Cmd != GntE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_661"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_87"
	(CurCmd != Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_955"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqS -> Chan1[j].Cmd != Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_370"
	(Chan1[i].Cmd = Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_802"
		(i != j) ->	(Chan1[i].Cmd = Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_238"
	(CurCmd != ReqE -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_228"
		(i != j) ->	(Chan1[j].Cmd = Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_848"
	(CurCmd = ReqS -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_311"
	(CurCmd != Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_220"
	(ShrSet[i] = false -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_30"
		(i != j) ->	(InvSet[j] = false -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_380"
	(Chan2[i].Cmd != GntS -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_490"
	(CurCmd = ReqS -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_283"
		(i != j) ->	(Chan2[i].Cmd != GntS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_452"
		(i != j) ->	(Chan2[i].Cmd != GntE -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_603"
		(i != j) ->	(Chan2[j].Cmd != GntS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_974"
		(i != j) ->	(Chan1[i].Cmd = ReqE & Chan1[j].Cmd = ReqE -> CurCmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_707"
	(Chan1[i].Cmd = ReqE -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_119"
		(i != j) ->	(Cache[j].State = I -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_496"
	(CurCmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_552"
	(Chan2[i].Cmd = GntE -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_164"
	(Cache[j].State != S -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_148"
		(i != j) ->	(ShrSet[i] = true -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_248"
	(CurCmd = ReqS -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_608"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_616"
		(i != j) ->	(Cache[i].State != E -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_908"
		(i != j) ->	(Chan1[j].Cmd = ReqS & CurCmd != Empty -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_737"
	(Chan1[j].Cmd != Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_600"
	(CurCmd = ReqS -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_565"
	(Chan2[i].Cmd != GntE -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_973"
		(i != j) ->	(Chan1[i].Cmd = ReqS & CurCmd != Empty -> Chan1[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_822"
	(Chan1[j].Cmd = ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_147"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_471"
		(i != j) ->	(ShrSet[i] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_205"
	(Chan2[i].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_226"
	(Chan1[i].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_110"
	(CurCmd != ReqE -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_947"
		(i != j) ->	(CurCmd = ReqS & Chan1[i].Cmd = ReqS -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_897"
	(Chan2[i].Cmd != GntS & ShrSet[i] = true -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_952"
		(i != j) ->	(Chan1[j].Cmd = ReqS & CurCmd != Empty -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_292"
	(ShrSet[i] = false -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_556"
	(CurCmd = Empty -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_757"
	(Chan1[j].Cmd != ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_804"
		(i != j) ->	(Chan2[j].Cmd != Inv -> Chan2[i].Cmd != Inv);
endruleset;
Invariant "rule_76"
	(ExGntd = true -> CurCmd = Empty);


ruleset i : NODE ; j : NODE do
Invariant "rule_173"
		(i != j) ->	(Chan2[i].Cmd != GntS -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_810"
		(i != j) ->	(Cache[j].State = I -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_586"
	(Chan1[i].Cmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_841"
		(i != j) ->	(Chan2[i].Cmd != GntE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_589"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_9"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_744"
		(i != j) ->	(Cache[i].State != S -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_491"
		(i != j) ->	(Chan2[i].Cmd = Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_916"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[i].Cmd = ReqS -> CurCmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_206"
	(Chan1[j].Cmd = ReqE -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_700"
	(Chan1[j].Cmd != Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_794"
	(CurCmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_506"
		(i != j) ->	(Chan1[j].Cmd != ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_711"
		(i != j) ->	(Chan1[j].Cmd = Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_483"
	(Chan1[j].Cmd = Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_195"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_951"
		(i != j) ->	(CurCmd = ReqS & Chan1[i].Cmd = ReqE -> Chan1[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_879"
	(CurCmd = Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_47"
		(i != j) ->	(Cache[j].State != S -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_175"
		(i != j) ->	(Cache[j].State != S -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_673"
	(CurCmd = ReqE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_154"
		(i != j) ->	(Cache[i].State != S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_636"
		(i != j) ->	(Cache[j].State = I -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_927"
		(i != j) ->	(CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan1[j].Cmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_943"
		(i != j) ->	(Chan1[i].Cmd = ReqS & Chan1[j].Cmd = ReqS -> CurCmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_480"
	(Cache[j].State = I -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_117"
	(Chan1[j].Cmd = ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_441"
		(i != j) ->	(Chan3[j].Cmd = Empty -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_559"
	(Chan2[j].Cmd != GntE -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_466"
	(ExGntd = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_888"
		(i != j) ->	(Chan1[i].Cmd = ReqE & Chan1[j].Cmd = Empty -> CurCmd != Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_612"
	(ExGntd = true -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_938"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[j].Cmd != ReqE -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_343"
	(Chan1[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_321"
	(Cache[j].State = I -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_591"
	(Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_541"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_236"
	(CurCmd = ReqS -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_696"
	(Chan2[i].Cmd = GntE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_305"
		(i != j) ->	(Cache[j].State != E -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_642"
	(Chan2[j].Cmd != GntS -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_134"
	(Chan1[i].Cmd = ReqE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_821"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_693"
		(i != j) ->	(Chan2[i].Cmd != Inv -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_361"
		(i != j) ->	(Chan2[i].Cmd = Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_564"
	(Chan1[i].Cmd = Empty -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_201"
	(Chan1[j].Cmd = ReqS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_133"
	(ExGntd = true -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_232"
	(CurCmd != ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_646"
		(i != j) ->	(Cache[i].State = I -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_825"
	(ShrSet[i] = true -> CurCmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_344"
	(CurCmd != ReqS -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_574"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_853"
		(i != j) ->	(Cache[i].State != S -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_622"
	(Chan2[i].Cmd != GntS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_153"
		(i != j) ->	(Chan2[j].Cmd != Inv -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_71"
	(Chan2[i].Cmd != Inv -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_872"
	(Chan1[i].Cmd = ReqE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_868"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_572"
	(Chan1[i].Cmd = ReqE -> ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_597"
	(CurCmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_921"
		(i != j) ->	(Chan1[i].Cmd != Empty & Chan1[j].Cmd = ReqE -> CurCmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_790"
		(i != j) ->	(Chan1[j].Cmd != ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_525"
	(Chan2[i].Cmd = Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_861"
		(i != j) ->	(Cache[j].State = I -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_670"
		(i != j) ->	(Chan2[i].Cmd = GntE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_644"
		(i != j) ->	(Chan2[j].Cmd = Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_235"
		(i != j) ->	(Chan1[i].Cmd = Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_518"
	(CurCmd = ReqS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_513"
	(Chan1[i].Cmd != ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_882"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_669"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_113"
	(Chan2[i].Cmd != GntE -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_866"
	(Chan2[j].Cmd != GntS -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_489"
	(Chan1[j].Cmd != ReqS -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_497"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_791"
	(CurCmd = ReqS -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_977"
		(i != j) ->	(Chan1[i].Cmd = ReqS & Chan1[j].Cmd = ReqS -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_436"
	(Chan2[i].Cmd = GntE -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_922"
		(i != j) ->	(Chan1[i].Cmd != Empty & Chan1[j].Cmd = ReqS -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_895"
		(i != j) ->	(CurCmd = ReqE & Chan1[j].Cmd = ReqE -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_774"
		(i != j) ->	(Chan2[i].Cmd = Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_741"
	(Chan3[i].Cmd != InvAck -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_969"
		(i != j) ->	(Chan1[i].Cmd = ReqS & Chan1[j].Cmd = ReqS -> CurCmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_836"
	(CurCmd = ReqS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_366"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_387"
		(i != j) ->	(Chan1[j].Cmd != ReqE -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_187"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_33"
	(Chan1[j].Cmd != ReqS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_267"
		(i != j) ->	(ShrSet[i] = false -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_179"
	(Chan2[i].Cmd = GntS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_585"
		(i != j) ->	(Chan1[j].Cmd != ReqS -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_239"
		(i != j) ->	(Chan1[j].Cmd != Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_198"
	(ShrSet[i] = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_562"
	(Chan2[i].Cmd != GntE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_90"
		(i != j) ->	(Chan3[i].Cmd = Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_539"
	(Chan2[j].Cmd = Empty -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_475"
	(Chan1[j].Cmd = ReqS -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_730"
		(i != j) ->	(Chan1[i].Cmd != ReqS -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_17"
	(Chan3[j].Cmd = Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_16"
	(CurCmd = Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_579"
		(i != j) ->	(ShrSet[j] = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_878"
		(i != j) ->	(Chan1[i].Cmd != Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_786"
	(Chan2[i].Cmd = Empty -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_446"
	(CurCmd = ReqE -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_111"
	(CurCmd != Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_451"
	(Chan1[i].Cmd != Empty -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_196"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_654"
	(Chan1[i].Cmd != Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_747"
	(CurCmd = Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_824"
		(i != j) ->	(Chan2[j].Cmd != GntE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_256"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_889"
		(i != j) ->	(Chan1[i].Cmd = ReqE & CurCmd != Empty -> Chan1[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_22"
	(ExGntd = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_320"
	(InvSet[j] = false -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_171"
	(Chan2[j].Cmd != Inv -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_312"
	(Chan3[i].Cmd != InvAck -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_530"
	(Chan2[i].Cmd != Inv -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_639"
		(i != j) ->	(Chan2[i].Cmd != GntE -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_502"
	(Chan1[j].Cmd != ReqE -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_160"
	(ExGntd = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_568"
	(Chan1[i].Cmd = ReqS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_268"
		(i != j) ->	(Cache[i].State != S -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_13"
		(i != j) ->	(Chan3[j].Cmd != InvAck -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_769"
		(i != j) ->	(Cache[i].State = I -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_937"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[i].Cmd = ReqE -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_261"
	(Chan2[j].Cmd != Inv -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_275"
	(ExGntd = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_723"
	(Cache[j].State != E -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_132"
	(Chan1[j].Cmd = ReqS -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_243"
	(Chan1[j].Cmd != ReqS -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_620"
	(ShrSet[i] = true -> Chan1[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_718"
	(Chan1[j].Cmd != Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_691"
		(i != j) ->	(Chan2[i].Cmd != GntE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_358"
	(Chan1[j].Cmd != ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_79"
	(ExGntd = false -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_269"
		(i != j) ->	(Chan2[j].Cmd != GntS -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_180"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_303"
	(Chan2[i].Cmd != Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_102"
		(i != j) ->	(ShrSet[i] = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_543"
		(i != j) ->	(Chan3[i].Cmd != InvAck -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_847"
	(Cache[j].State != E -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_858"
	(CurCmd != ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_143"
	(ExGntd = false -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_424"
	(CurCmd != ReqS -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_875"
		(i != j) ->	(Chan3[i].Cmd = Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_266"
	(ShrSet[i] = false -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_271"
	(Cache[j].State != E -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_918"
		(i != j) ->	(Chan1[i].Cmd = ReqS & CurCmd != Empty -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_739"
	(Chan1[i].Cmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_253"
	(Chan3[i].Cmd = Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_596"
	(Chan1[i].Cmd != ReqE -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_165"
	(ExGntd = true -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_460"
	(CurCmd != ReqE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_245"
		(i != j) ->	(Chan1[j].Cmd != ReqS -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_887"
	(Chan2[i].Cmd != GntS & ExGntd = false -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_905"
		(i != j) ->	(CurCmd = ReqE & Chan1[i].Cmd = ReqE -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_75"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_421"
	(CurCmd != ReqE -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_158"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_499"
		(i != j) ->	(Cache[j].State != E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_576"
		(i != j) ->	(Chan3[j].Cmd != InvAck -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_123"
	(ExGntd = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_437"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_915"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[i].Cmd = ReqS -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_413"
	(CurCmd != ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_941"
		(i != j) ->	(CurCmd = ReqE & Chan1[j].Cmd != Empty -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_862"
	(Chan1[i].Cmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_738"
	(Chan1[i].Cmd != ReqS -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_431"
	(CurCmd = ReqE -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_100"
	(CurCmd != ReqS -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_263"
	(Chan2[i].Cmd = GntS -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_423"
	(Chan1[j].Cmd != ReqE -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_124"
	(CurCmd != Empty -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_270"
	(Chan2[j].Cmd = Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_528"
	(ShrSet[i] = true -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_74"
	(ShrSet[i] = true -> Chan1[i].Cmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_350"
		(i != j) ->	(Chan2[i].Cmd = GntS -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_681"
	(Cache[j].State = I -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_838"
	(ExGntd = true -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_724"
	(Chan1[i].Cmd = ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_52"
	(Chan1[i].Cmd = ReqS -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_149"
	(CurCmd = ReqE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_385"
		(i != j) ->	(InvSet[i] = false -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_534"
		(i != j) ->	(InvSet[i] = false -> Chan3[j].Cmd != InvAck);
endruleset;
Invariant "rule_139"
	(ExGntd = true -> CurCmd != ReqS);


ruleset i : NODE ; j : NODE do
Invariant "rule_692"
		(i != j) ->	(Chan3[j].Cmd = Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_101"
	(Chan2[i].Cmd = GntE -> CurCmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_932"
		(i != j) ->	(Chan1[j].Cmd != Empty & CurCmd != Empty -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_213"
	(Chan1[i].Cmd != ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_294"
	(CurCmd != Empty -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_813"
	(CurCmd != ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_63"
	(ExGntd = true -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_702"
	(Chan1[j].Cmd = ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_760"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_694"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_25"
	(InvSet[j] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_382"
		(i != j) ->	(Chan2[i].Cmd != GntS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_392"
		(i != j) ->	(ShrSet[i] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_850"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_316"
	(Chan2[i].Cmd = GntS -> CurCmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_538"
	(Chan3[i].Cmd = Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_598"
		(i != j) ->	(Chan1[i].Cmd = ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_902"
		(i != j) ->	(CurCmd = ReqE & Chan1[i].Cmd = ReqS -> Chan1[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_56"
	(CurCmd = Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_363"
	(CurCmd = Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_276"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_801"
	(Chan1[j].Cmd != Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_812"
	(Chan1[j].Cmd != ReqS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_788"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_911"
		(i != j) ->	(Chan1[i].Cmd = ReqS & CurCmd != Empty -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_961"
		(i != j) ->	(CurCmd = ReqE & Chan1[i].Cmd != Empty -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_837"
	(CurCmd != Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_461"
	(Chan3[i].Cmd != InvAck -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_331"
	(Cache[j].State = I -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_302"
	(CurCmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_4"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_15"
	(ShrSet[i] = true -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_957"
		(i != j) ->	(CurCmd = ReqS & Chan1[i].Cmd != Empty -> Chan1[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_714"
	(ExGntd = true -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_906"
		(i != j) ->	(CurCmd = ReqS & Chan1[i].Cmd != Empty -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_458"
		(i != j) ->	(Chan2[i].Cmd != Inv -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_814"
	(Chan1[i].Cmd = ReqE -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_742"
	(Cache[i].State != S -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_405"
	(Chan2[i].Cmd != Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_393"
	(Chan3[i].Cmd = Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_508"
	(CurCmd = Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_909"
		(i != j) ->	(CurCmd = ReqS & Chan1[i].Cmd = ReqE -> Chan1[j].Cmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_262"
	(ShrSet[j] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_621"
	(CurCmd = ReqE -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_549"
	(Chan1[i].Cmd = Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_416"
		(i != j) ->	(Chan2[i].Cmd != GntE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_116"
		(i != j) ->	(Cache[j].State != E -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_857"
	(CurCmd = ReqE -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_663"
		(i != j) ->	(Chan2[j].Cmd != GntE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_820"
	(Chan2[j].Cmd != GntS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_633"
	(CurCmd != Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_364"
	(CurCmd = ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_907"
		(i != j) ->	(Chan1[i].Cmd != Empty & Chan1[j].Cmd = ReqS -> CurCmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_956"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[i].Cmd = ReqS -> CurCmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_109"
	(CurCmd = Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_91"
		(i != j) ->	(Chan1[i].Cmd != Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_873"
	(CurCmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_652"
	(Chan2[j].Cmd != Inv -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_864"
		(i != j) ->	(Chan1[i].Cmd = ReqE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_72"
		(i != j) ->	(Cache[i].State != E -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_372"
	(Chan2[i].Cmd != Inv -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_336"
	(Chan1[j].Cmd != ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_512"
	(Chan2[i].Cmd = GntE -> CurCmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_45"
	(ExGntd = true -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_121"
		(i != j) ->	(Cache[i].State != E -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_330"
	(Chan3[j].Cmd = Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_798"
		(i != j) ->	(Chan1[j].Cmd = ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_683"
	(CurCmd = ReqE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_787"
	(ShrSet[i] = false -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_114"
	(Chan1[i].Cmd != ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_390"
	(Chan1[j].Cmd = ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_972"
		(i != j) ->	(Chan1[i].Cmd = ReqS & Chan1[j].Cmd = Empty -> CurCmd != Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_863"
	(Chan2[i].Cmd = GntS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_948"
		(i != j) ->	(Chan1[i].Cmd != Empty & Chan1[j].Cmd = Empty -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_335"
		(i != j) ->	(Chan1[i].Cmd != ReqE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_735"
	(Cache[j].State != S -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_755"
	(Chan1[j].Cmd = ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_199"
	(ShrSet[i] = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_527"
		(i != j) ->	(Chan3[j].Cmd = Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_843"
		(i != j) ->	(Chan2[i].Cmd = Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_548"
	(ShrSet[i] = false -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_177"
	(ExGntd = false -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_65"
	(InvSet[j] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_859"
		(i != j) ->	(Chan1[j].Cmd = Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_550"
	(Chan1[i].Cmd != Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_946"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[i].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_64"
	(Chan3[j].Cmd = Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_455"
	(Chan2[i].Cmd != GntE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_935"
		(i != j) ->	(CurCmd = ReqS & Chan1[j].Cmd = ReqE -> Chan1[i].Cmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_200"
		(i != j) ->	(Chan1[j].Cmd = ReqS -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_365"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_936"
		(i != j) ->	(Chan1[i].Cmd != Empty & Chan1[j].Cmd = ReqE -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_672"
	(CurCmd = ReqE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_919"
		(i != j) ->	(Chan1[i].Cmd != Empty & CurCmd != Empty -> Chan1[j].Cmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_35"
	(Chan1[i].Cmd != ReqE -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_945"
		(i != j) ->	(Chan1[j].Cmd != Empty & Chan1[i].Cmd != Empty -> CurCmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_885"
	(Chan1[j].Cmd = Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_126"
		(i != j) ->	(Chan1[j].Cmd != ReqS -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_914"
		(i != j) ->	(Chan1[i].Cmd = ReqS & Chan1[j].Cmd = ReqE -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_274"
	(CurCmd != ReqS -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_467"
	(ExGntd = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_964"
		(i != j) ->	(CurCmd = ReqS & Chan1[j].Cmd = ReqS -> Chan1[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_142"
		(i != j) ->	(Chan3[j].Cmd = Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_800"
	(Chan1[i].Cmd != ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_324"
	(Chan3[j].Cmd = Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_779"
	(Chan1[i].Cmd = ReqE -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_293"
	(CurCmd = Empty -> Chan3[i].Cmd = Empty);
endruleset;
