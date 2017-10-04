/*********************************************
 * OPL 12.7.1.0 Model
 * Author: jpierreber
 * Creation Date: 4/10/2017 at 12:03:12
 *********************************************/
/*********************************************
 * OPL 12.7.1.0 Data
 * Author: jpierreber
 * Creation Date: 4/10/2017 at 12:03:36
 
 //only problem: we have to force the model to visit at least to locations per trip otherwise it does not go everywhere
 *********************************************/

 
  //datos del problema//
int n=...;
range proved= 0..n; 

int p=...; 
range product= 0..p;
 
int t=...;
range period=1..t;


// numero, peso y  volumen de los vehiculos 
int k=...;
range vehicle=1..k; 

int Q=...;


//storage capacity per product
int S[proved]=...;

int kilometros [proved,proved]=...;
int demanda[product,period]=...;

////////////////////////////////
 // DEFINIR VARIABLES DE DECISION
// 1 si el arco i,j es atravesado por el vehiculo k, 0 sino.
dvar boolean x [proved][proved][vehicle][period];

// La carga del vehiculo (peso) acumulada.
//dvar float+ u[proved][vehicle][period];

// quantity transported 
dvar int+ q [proved][proved][product][vehicle][period];

// Activacion de los vehiculos (binary)
dvar boolean y[proved][vehicle][period];

/////NEW VARIABLES DECISIONS///////
//Inventory level of supplier i to the end of period t
 dvar float+ Inv [proved][product][period];

 //Amount to picked-up of suppier i in the period t
 dvar int+ a[proved][product][period];
 
 
 ///////////////////   
 // Modelo mat
 
 minimize   
 sum(i in proved, j in proved, k in vehicle, t in period) kilometros[i,j]*x[i,j,k,t];
 
  ////////////////////////////////
 //RESTRICCIONES
 

 subject to {

	
// 2a orig inv of suppliers	
//pro
//forall(i in 2..n:i!=p, t in period)
  //	Inv[i,p,t]==Inv[i,p,t-1]-a[i,p,t];

// 2b orig inv of suppliers	without i is not p constraint and without t=1 	
forall(i in 2..n:i!=p, t in 2..t)
  	Inv[i,p,t]==Inv[i,p,t-1]-a[i,p,t];
  	
// 2c add: starting inventory suppliers
forall(i in 2..n, p in product:i==p)
  	Inv[i,p,1]==1000;
  	//Inv[i,p,0]==10000;
  	
// 2d add: starting inv suppliers is 0 when the supplier number and product number don't match 	
forall(i in 2..n, p in product:i!=p, t in period)
  	Inv[i,p,t]==0;

//2e  	
forall(p in product)
   Inv[0,p,1]==0;
  	  

//3a orig
//forall (p in product, t in period)
  //Inv[0,p,t]==Inv[0,p,t-1]+sum(i in 2..n, k in vehicle)q[i,0,p,k,t]-demanda[p,t];

//3b inv of depot from period 2 
forall (p in product, t in 2..t)
  Inv[0,p,t]==Inv[0,p,t-1]+sum(i in 2..n, k in vehicle)q[i,0,p,k,t]-demanda[p,t];
  
// 3c inv depot period 1 
//forall (p in product)
//  Inv[0,p,1]==sum(i in 2..n, k in vehicle)q[i,0,p,k,1]-demanda[p,1];
  
//4 orig: each supplier should not be visited more than once 
//forall (i in 2..n, k in vehicle, t in period)
  //sum(j in proved)x[j,i,k,t]== sum(j in proved)x[i,j,k,t]==y[i,k,t];
  
forall (i in 2..n, k in vehicle, t in period)
  sum(j in proved)x[j,i,k,t]== sum(j in proved)x[i,j,k,t];
  
forall (i in 2..n, k in vehicle, t in period)  
  sum(j in proved)x[i,j,k,t]==y[i,k,t];
  
//5 orig: each supplier should not be visited more than once 
forall(i in 2..n, t in period)
  sum(k in vehicle)y[i,k,t]<=1;

//6a orig: inventory balance for suppliers (what leaves the node+ what was picked up=what was there before??)
forall(i in 2..n, p in product, t in period)
  //sum(j in proved, k in vehicle)q[j,i,p,k,t]-a[i,p,t]==sum(j in proved, k in vehicle)q[i,j,p,k,t];
  sum(j in 1..n, k in vehicle)q[j,i,p,k,t]+a[i,p,t]==sum(j in proved:j!=1, k in vehicle)q[i,j,p,k,t];

//6b adj: inventory balance for suppliers (what leaves the node+ what was picked up=what was there before??)
//forall(j in 2..n, p in product, t in period)
  //sum(i in 1..n, k in vehicle)q[i,j,p,k,t]+a[j,p,t]==sum(i in 1..n, k in vehicle)q[j,i,p,k,t];


//7 orig
forall(i in proved, j in proved, k in vehicle, t in period)
  sum(p in product)q[i,j,p,k,t]<= Q*x[i,j,k,t];
  
//8a orig
//forall(i in 2..n: p!=i, t in period)
  //a[i,p,t]<=Inv[i,p,t-1];
  
  //8b adj
forall(i in 2..n, t in 2..t)
  a[i,p,t]<=Inv[i,p,t-1];
  
//9a orig nr of veh avail
//forall(k in vehicle, t in period)
  //sum(i in 2..n)x[1,i,k,t]<=k;
  
//9b adj
forall(t in period)
  sum(i in 2..n, k in vehicle)x[1,i,k,t]<=k;
  
//10a  orig number of vehilces leaving fictious node !pro
forall(t in period)
  sum(j in 2..n, k in vehicle)x[1,j,k,t]>=1;
  
//10b add
//forall(j in proved, k in vehicle, t in period)
  //sum(i in 1..1)x[i,j,k,t]>=1;
  
//11a orig number of vehilces entering depot 
//forall(k in vehicle, t in period)
  //sum(i in 2..n)x[i,0,k,t]>=1;
  
//11b add number of vehilces entering depot 
forall(t in period)
  sum(i in 2..n, k in vehicle)x[i,0,k,t]>=1;

//14a orig no route from depot pro
forall (i in 2..n, k in vehicle, t in period)
  x[0,i,k,t]==0; 
  
// 14b add no route to fictious node  
 forall(i in proved, k in vehicle, t in period)
  x[i,1,k,t]==0;
  
//15  orig no route between same node
//forall(i in proved, k in vehicle, t in period)
  //x[i,i,k,t]==0; 
  
// 16a orig no route  fictious node to depot
forall(k in vehicle, t in period)
  x[1,0,k,t]==0;
  
//16b adj  no route from depot pro
//forall(j in proved, k in vehicle, t in period)
  //x[0,j,k,t]==0;
  
//17a orig do not bring stuff from depot? 
forall(j in proved, p in product, k in vehicle, t in period)
  q[0,j,p,k,t]==0;
  
//17b adj do not bring stuff to fictious node
forall(i in proved, p in product, k in vehicle, t in period)
  q[i,1,p,k,t]==0;
  
//18 orig 
forall(i in proved, p in product, t in period)
	a[i,p,t]>=0;
   
  
//own constraints

 
//add1: vehicles leaving fictious = vehicles entering depot
//forall(i in 2..n, j in 2..n, t in period)
  //sum(k in vehicle)x[1,j,k,t]==sum(k in vehicle)x[i,0,k,t];
  
//add2 positive inventory for depot////problem
  //forall(i in proved, p in product, t in 2..t)
  //Inv[0,p,t]>=0;
  
//add4 min stops per route
//forall(k in vehicle,t in period)
  //sum(i in 1..n, j in 1..n)x[i,j,k,t]<=6;
  
//add5 extra sec 30 years inv routing (eq. 12 sec)
//forall(i in proved, m in proved, k in vehicle, t in period)
  //sum(i in proved, j in proved: i<j)x[i,j,k,t]<=sum(i in proved)y[i,k,t]-y[m,k,t];
  
  
//?add 6AleksHeleen: all trucks driving around, have started in i=1
//forall(i in proved, k in vehicle, t in period)
  //sum(j in 2..n)x[i,j,k,t] <= n*sum(j in 2..n)x[1,j,k,t];
  
  
//add7 all trucks driving around, have started in i=1
forall(i in proved, k in vehicle, t in period)
  sum(j in 2..n)x[1,j,k,t] <= y[1,k,t];   


 //add 8forall(j in proved, k in vehicle, t in period)
  //sum(i in 2..n)x[i,0,k,t] <= y[j,k,t] ;
   
  //a14  
// add truck that enters a node should be same as the one that leaves
forall(i in 2..n, k in vehicle, t in period)
  sum(j in 2..n: i<j)x[i,j,k,t]==sum(j in 2..n: j<i)x[j,i,k,t];
  
  //a15
//4 add: balance constraint '30 years of inventory routing '  
//forall(i in proved, k in vehicle, t in period)
  //sum(j in proved:i<j)x[i,j,k,t]+sum(j in proved:i>j)x[j,i,k,t]==2*y[i,k,t];
 
//a17 use one vehicle once per day
forall(k in vehicle, t in period)
  sum(j in 2..n)x[1,j,k,t]<=1;
  
//add 9 //Solo, entra y sale un arco de cada vertice
forall (i in 2..n, t in period) {
sum (j in proved, k in 1..k) x[i,j,k,t] >= 1;

forall ( j in 2..n,t in period)
sum (i in proved,k in 1..k) x[i,j,k,t] >= 1;

forall( k in 1..k,t in period)
x[i,i,k,t] == 0;
}

//add10 don't pick up stuff from places that don't have that product (doesn't work)
forall(i in 2..n, p in product:i!=p, t in period)
  a[i,p,t]==0;

//add11 no stuff brought from fictious node
forall(j in proved, p in product, k in vehicle, t in period)
	q[1,j,p,k,t]==0;

}
 

 