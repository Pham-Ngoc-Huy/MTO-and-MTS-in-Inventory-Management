/*********************************************
 * OPL 12.8.0.0 Model
 * Author: admin
 * Creation Date: Apr 26, 2023 at 2:01:32 AM
 *********************************************/
int 	k = 2; // level pricing fabric
int 	nmts = 15; // the number of type of MTS
int 	nmto = 10;  // the number of type of MTO
int 	tf = 5; // the number of type of fabric
int 	np = 12; //number period
range 	rmts= 1..nmts; //range MTS
range 	rmto= 1..nmto; //range MTO
range 	rf = 1..tf; // range type of fabric
range 	rp = 0..np; //range period
range 	rk = 1..k; //range level pricing fabric
float 	ICF[rf][rp]=...; //holdingcost fabric taken from excel 
float 	ICO[rmto][rp]=...; //holdingcost MTO taken from excel
float 	ICS[rmts][rp]=...; //holdingcost MTS taken from excel
int   	IFA[rf]=...; //inventory of each type of fabric at period= 0
int   	IS[rmts] =...; //inventory of each type of MTS products at period 0 
float   RCO[rmto]=...; // regualar time production cost per unit of each m MT0 products
float   RCS[rmts]=...; // regular time productiong cost per unit of each j MTS products
float   OCO[rmto]=...; // overtime productioen cost per unit of m product MTO
float   OCS[rmts]=...; // overtime production cost perunit  of j prodcuc MTS 
float   SBC[rmto][rp]=...; // subcontracting cost for each m MTO product at each period
float   AFO[rf][rmto]=...; //amount of fabric f to make one unit of MTO product m
float   AFS[rf][rmts]=...; // amount of fabric f to make one unit of MTS product j
float   HO[rmto]=...; // labor hour needed to process one unit of product m of MTO
float   HS[rmts]=...; // labor hour needed to process one unit of product j of MTS
int   	HMAX = 260; //maximum available regular production hours per period
int   	GMAX = 10; // maximim available overtime production hour per period
float   WF[rf]=...;// warehouse space needed per meter of each fabric f
float   WFMAX=40; // maximum fabric warehouse capacity (m2)     
float   VO[rmto]=...; //storage space requirement per unit of finshed MTO product m
float   VS[rmts]=...; //storage space requirement per unit of finshed MTS product j 
float   VMAX=50   ; //maximum storage space for MTO and MTS
int     DM[rmto][rp]=...; // demand based on confirmed orders MTO
int     FJ[rmts][rp]=...;// forcasted demand MTS
int   	PO[rmto]=...;// sellimg price of one unit of MTO product m
int   	PS[rmts]=...;// selling price of one unit of MTS product j
int     RF[rf][rk]=...;// purchase price r of fabric f at level k
int     QF[rf]=...;// minimum of meters fabric to get discount (m2)
int     BO[rmto]=...;//minimum batch size for production of MTO product m
int     BS[rmts]=...;//minimum batch size for production of MTS product j
int   CO = 200000;//initial cash available at the beginning  of the planning horizon
int   CT = 1000000;// minimum final cash targeted at the end of the planning horizon 
int     L  = 1000;// a large possitive number

//define decision variable 
dvar int+ 	FQ[rf][rk][rp]; //Area of fabric f ordered at price level k during period t (m2)
dvar int+ 	IA[rf][rp]; //Area of fabric f kept in inventory by the end ofperiod t (m2).
dvar int+ 	CH[rp]; //Cash available by the end of period t
dvar float+ 	ILO[rmto][rp];//WIP Inventory level of MTO product m by the end of period t
dvar int+ 	ILS[rmts][rp];//WIP Inventory level of MTS product j by the end of period t
dvar int+ 	RO[rmto][rp];// Regular time production quantity of MTO product m during period t
dvar int+ 	RS[rmts][rp];//Regular time production quantity of MTS product j during period t
dvar int+  	OP[rmto][rp];//overtime production quantity of MTO product m during period t
dvar int+  	SP[rmts][rp];//overtime production quantity of MTS product j during period t
dvar int+  	S[rmto][rp];//Subcontracting amount of product m at timeperiod t
dvar boolean   B[rf][rp];// if fabric f is purchase for price level k = 2, in time period t and = 0 otherwise.
dvar boolean   F[rmto][rp];// =1; if MTO product m is produced during period t, and = 0 otherwise
dvar boolean   F1[rmts][rp];//=1; if MTS product j is produced during period t, and = 0 otherwise 

dvar int+ I[rp];
execute PRE_PROCESSING {
 cplex.epgap = 0.1 ;
 cplex.tilim = 100 ;
}
//define objective function
maximize sum(m in rmto,t in rp) PO[m]*DM[m][t] + sum(j in rmts,t in rp) PS[j]*FJ[j][t]
- sum(m in rmto) RCO[m]* sum(t in rp) RO[m][t]- sum(m in rmto) OCO[m]*sum( t in rp) OP[m][t]
- sum(j in rmts) RCS[j]*sum(t in rp) RS[j][t]- sum(j in rmts) OCS[j]*sum( t in rp) SP[j][t]
- sum(f in rf,k in rk, t in rp) RF[f][k]*FQ[f][k][t]-sum(m in rmto,t in rp)ICO[m][t]*ILO[m][t]
- sum(j in rmts,t in rp)ICS[j][t]*ILS[j][t]-sum(t in rp, f in rf) ICF[f][t]*IA[f][t]
- sum(t in rp,m in rmto) SBC[m][t]*S[m][t];



//constraint:
subject to
{
c1 :forall (f in rf, t in rp: t == 0){
  IA[f][t] == IFA[f];
} 																		//(2)		
c2 :forall(f in rf, k in rk, t in rp){
IA[f][0] + FQ[f][k][0] 
  - sum(i in rmto)AFO[f][i]*(RO[i][0] + OP[i][0]) 
  - sum(j in rmts)AFS[f][j] *(RS[j][0]+ SP[j][0]) == IA[f][0];
  if(t>0)

  IA[f][t-1] + FQ[f][k][t] 
  - sum(i in rmto)AFO[f][i]*(RO[i][t] + OP[i][t]) 
  - sum(j in rmts)AFS[f][j] *(RS[j][t]+ SP[j][t]) == IA[f][t];
}   																		//(3)
c3 :forall (j in rmts, t in rp: t == 0){
	ILS[j][t] == IS[j];
} 																			//(4)
c4 :forall(j in rmts, t in rp )
{
	(RS[j][0] + SP[j][0]) - ILS[j][0] == FJ[j][0]; 
	if (t > 0  )	
		 (RS[j][t] + SP[j][t]) + ILS[j][t-1] - ILS[j][t] <= FJ[j][t];
}																 			//(5)
c5 :forall(m in rmto, t in rp){
    ILO[m][0] + RO[m][0] + OP[m][0] + S[m][0] == DM[m][0] + ILO[m][0];
    if (t>0)

	ILO[m][t - 1] + RO[m][t] + OP[m][t] + S[m][t] == DM[m][t] + ILO[m][t];
}																			//(6)
c6 :forall(t in rp){
	sum(m in rmto) HO[m]*RO[m][t] + sum(j in rmts) HS[j]*RS[j][t] <= HMAX;
}																		 	//(7)
c7 :forall(t in rp){
	sum(m in rmto) HO[m]*OP[m][t] + sum(j in rmts) HS[j]*SP[j][t] <= GMAX;
}																		 	//(8)
c8 :forall(t in rp: t>=1 &&t<=12){
	sum(f in rf) WF[f]*IA[f][t] <= WFMAX;
}										 									//(9)
c9 :forall(t in rp: t>=1 &&t<=12){
	sum(m in rmto) VO[m]*ILO[m][t] 
	+ sum(j in rmts) VS[j]* ILS[j][t] <= VMAX;
} 																			//(10)
c10 :forall(f in rf, k in rk, t in rp: k == 1){
	FQ[f][k][t] <= QF[f]*B[f][t];
}																			//(11)
c11 :forall(f in rf, k in rk, t in rp: k == 2 ){
  	QF[f]*(1 - B[f][t]) <= FQ[f][k][t];
}								  											//(12)
c12 :forall(t in rp:t == 0){
  	CH[t] == CO;			
}						  													//(13)
c13 :forall(f in rf, k in rk, t in rp: t<=4 && t>=1){
	CH[t-1] + sum(m in rmto) PO[m] * DM[m][t] 
	- sum(f in rf) RF[f][k]*FQ[f][k][t]
	- sum(m in rmto)(RCO[m]*RO[m][t] + OCO[m]*OP[m][t])
	- sum(j in rmts)(RCS[j]*RS[j][t] + OCS[j]*SP[j][t])
	- sum(m in rmto) SBC[m][t]*S[m][t] == CH[t];
}												 							//(14)
c14 :forall(f in rf, k in rk, t in rp: t >=5 && t<=12){
	CH[t-1] + sum(m in rmto) PO[m] * DM[m][t] 
	+ sum(j in rmts) PS[j] * FJ[j][t] 
	- sum(f in rf) RF[f][k]*FQ[f][k][t]
	- sum(m in rmto)(RCO[m]*RO[m][t] + OCO[m]*OP[m][t])
	- sum(j in rmts)(RCS[j]*RS[j][t] + OCS[j]*SP[j][t])
	+ sum(m in rmto) SBC[m][t]*S[m][t] == CH[t];
}																			//(15)
c15 :forall(t in rp: t==12){	
	CH[t] >= CT;			
}																			//(16)
c16 :forall(m in rmto, t in rp){
  	RO[m][t] + OP[m][t] >= BO[m]*F[m][t];
}									  										//(17)
c17 : forall(m in rmto, t in rp){
  	F[m][t]  >= 1/L * sum(m in rmto)(RO[m][t] + OP[m][t]);
}													  						//(18)
c18 :forall(j in rmts, t in rp){
	RS[j][t] + SP[j][t] >= BS[j]*F1[j][t];
}																			//(19)
c19 :forall(j in rmts, t in rp){
  	F1[j][t] >= 1/L * sum(j in rmts)(RS[j][t] + SP[j][t]);
}
forall(f in rf, k in rk, t in rp: 1 <= t <= 12)
  	FQ[f][k][t] >= 0;
forall(f in rf, t in rp:  1 <= t <= 12)
  	IA[f][t] >= 0;
forall(t in rp:  1 <= t <= 12)
  	CH[t] >= 0;
forall(m in rmto, t in rp:  1 <= t <= 12)
  	ILO[m][t] >= 0;
forall(j in rmts, t in rp:  t == 0)
  	ILS[j][t] ==0; 	
forall(j in rmts, t in rp:  1 <= t <= 12)
  	ILS[j][t] >= 0;
forall(m in rmto, t in rp:  1 <= t <= 12)
  	RO[m][t] >= 0;
forall(j in rmts, t in rp:  1 <= t <= 12)
  	RS[j][t] >=0;
forall(m in rmto, t in rp:  1 <= t <= 12)
  	OP[m][t] >=0;
forall(j in rmts, t in rp:  1 <= t <= 12)
   	SP[j][t] >= 0;
}


 