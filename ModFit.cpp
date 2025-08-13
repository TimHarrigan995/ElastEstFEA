/* ********************************************
    program to do modulus estimates
      using finite element analysis

           by Timothy P. Harrigan

    DISCLAIMER: I guarantee nothing.  The responsibility for
         any use or modification of this code lies entirely with
         the user. Check everything.

 *********************************************  */




/* main program for finite element analysis  */
#include "stdio.h"
#include <math.h>
#include <malloc.h>
/* SGI version
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <ulocks.h>
*/
#include <time.h>

void diagtrans(int *, int);
void colheight(int, int *, int *);
double elstend(int *,double *,double *,int,double,double *);
void eldisdot(int *,double *,double *,int,double *);
void elcalc(int,int,int,int,int *,int *, double *);
void elforce(int,int,int,int,int *,int *);
 int canceldofs(int *, int *, int, int);
 int blockalloc(int* colptr,int ndoftot,FILE *output);
 int plinsolv(double *stifptr,double *loadptr,int *colptr,int ndoftot,double *workptr,int nint,FILE *output);
 int addel(int dof[],double elstf[],double matrix[],int diags[],int neq,int nel);
 int threedsolid(int nel,int nnodes,int nint, double matpass[],double elnpc3[][3],double s[],FILE *output,
		 double *volume,double gammar,double transexpnt);
 int twodsolid(int nel,int nnodes,int itype,int nint,double matprops[4],double xx[][2],double s[],FILE *output,
 		double *volume,double gammar,double gexpnt);

 int maxcolht,ndoftot,nlcase;
double *coorptr,  *loadptr, *workptr, *matptr, *nsptr;
double modexpnt,transexpnt,nulstate,dtime,gamnorm,ratenorm,dgamnorm,tol,itol;
double oblnorm,mdisp;
double *phiptr,*rateptr,*relvol,*mdisptr;

int *colptr;

double *elnodf,*eldiag;
double *alpha;

static FILE *output,*ebfile;
static FILE *input,*disdens,*loadfile;

int eldone[4], netmaxdel,blalcdone,numrel;

int main()
{

double *stifptr;
int *dofptr;
char title[80];
int c,c2,c3,c4,c5,n,dof,doftot,dmy,eldmy,df,dofx,dofy,dofz;
double x,y,z,lmag,e,nu,ux,uy,uz,thic,volume,ddmy;
int elnod, mpnum,elsize,offset,memsize,nodnum;
int numel, eltyp, maxnodes, memelem,maxmelem;
int lnode, ldof,matlsize,mtype,maxdel,itype,netact;
int ncase, netdof,nloads, fstatus, rstatus, wstatus, solstat;
int remflag,rind,r,ind,iter,itermax, doneflag,ebstart,nupper;
int ntnodes,masterdof,nelgps,matsize,nmatp,error;
int *eldat,*eldof,*remdiags;

int nts,nsizes,*breakstep;
double *stepsiz,netime;



int prnum,eldstart,tst,ct;

int **elarry;

double gfrac1,gfrac2,modinv,phi,phinorm;

clock_t tstart,tinput,tend;
double cpuinp,cpuproc,tchange;

/* **************************************************************************


     INPUT PHASE:

   get input data:
       number of nodes,
       DOF per node,
       number of load cases,
       number of element groups

   **********************************************************************   */

tstart=clock();

maxmelem=0;
netmaxdel=0;
itermax=20;
iter=0;
blalcdone=0;
/* open files */

input=fopen("/home/tim/elast/FEINFILE", "r");
output=fopen("FEOUTFILE", "w");
disdens=fopen("FEDISDENS", "w");

ebfile=fopen("EBMAT", "w+");
loadfile=fopen("FELOADS", "w+");

/* read in overal control data */

c=0;
while((title[c++]=fgetc(input))!= '\n');

fscanf(input,"%d %d %d %d",&ntnodes,&masterdof,&nlcase,&nelgps);

//elarry = calloc(nelgps*2,sizeof(eldat));
elarry=new int*[nelgps*2]();

/* print up a nice looking header for the output file */

fprintf(output," ********************************************************\n");
fprintf(output,"\n\n      A LINEAR ELASTIC FINITE ELEMENT PROGRAM\n");
fprintf(output,"  FOR MODULUS ESTIMATION STUDIES \n");
fprintf(output,"     WRITTEN BY TIM HARRIGAN - FIRST REVISION 6/6/91\n\n");

/* *************************************************************************
   get memory for nodal point coordinates
              and degrees of freedom
   **********************************************************************    */

//coorptr=calloc(ntnodes*3, sizeof((double)0));
coorptr=new double[ntnodes*3]();
if(coorptr == NULL)printf("coordinate allocation failed (main)\n");

//dofptr =calloc(ntnodes*3, sizeof((int)0));
dofptr=new int[ntnodes*3]();
if(dofptr == NULL)printf("degree of freedom allocation failed (main)\n");

//mdisptr=calloc(ntnodes*3,sizeof((double)0));
mdisptr= new double[ntnodes*3]();
/* **********************************************************************
   read in nodal points
   **********************************************************************    */

fprintf(output," Nodal Point Degrees of Freedom and Coordinates\n\n");
fprintf(output,
   "  n  xdof  ydof  zdof         x             y            z\n\n");

ndoftot=1;
for(c=0;c<ntnodes;c++){
  fscanf(input, " %d %d %d %d %lf %lf %lf",&n,&dofx,&dofy,&dofz,&x,&y,&z);
    dmy=3*(n-1);
  if(n<=ntnodes){
    coorptr[dmy]=x;
    coorptr[dmy+1]=y;
    coorptr[dmy+2]=z;
    dofptr[dmy]=dofx;
    dofptr[dmy+1]=dofy;
    dofptr[dmy+2]=dofz;
    if(dofx>0)ndoftot++;
    if(dofy>0)ndoftot++;
    if(dofz>0)ndoftot++;
  }  /* if */
fprintf(output," %5d %5d %5d %5d %12.9lf %12.9lf,%12.9lf\n",
   n,dofptr[dmy],dofptr[dmy+1],dofptr[dmy+2],x,y,z);
} /* for */

/* ***************************************************************
   get memory for column heights
   ***************************************************************     */

//colptr= calloc(ndoftot+2, sizeof((int)0));
colptr=new int[ndoftot + 2];
if(colptr == NULL)printf("column pointer allocation failed (main)\n");

/* ***************************************************************

   LOOP THROUGH ELEMENT GROUPS

   read in element information
      to get the matrix profile
      and remodelling element indices
      then store the information on disk

   ***************************************************************    */

numrel = 0;
rind=0;

for(c=0;c<nelgps;c++){

  fscanf(input," %d %d %d %d", &numel,&eltyp,&maxnodes,&remflag);

  if(remflag == 1)numrel+= numel;

    //elarry[c*2]=calloc(4,sizeof((int)0));
    elarry[c*2]=new int[4]();

    eldat=elarry[c*2];

    if(eldat == NULL)printf("element group data allocation failed (main)\n");

  eldat[0]=numel;
  eldat[1]=eltyp;
  eldat[2]=maxnodes;
  eldat[3]=remflag;


/* define netmaxdel = maximum element degrees of freedom
   for later use in remodelling iterations */

  if(eltyp/10 == 2){
      maxdel=maxnodes*2;}
  if(eltyp == 3){
      maxdel=maxnodes*3;}

netmaxdel = (maxdel >netmaxdel) ? maxdel : netmaxdel;


/* *****************************************************************
   get memory for element info
   ******************************************************************   */

  if(eltyp == 3)elsize= 4 + maxnodes*4;
  if(eltyp/10 == 2)elsize= 4 + maxnodes*3;

  memelem = numel*elsize;

  //elarry[c*2 +1]=calloc(memelem, sizeof((int)0));
  elarry[c*2+1]=new int[memelem]();
   eldat=elarry[c*2 + 1];

  if(eldat == NULL)printf("element data allocation failed (main)\n");


/* ********************************************************************
     read in elements,
       send info to column height routine,
       store elements for later
    *******************************************************************  */

  for(c2=0;c2<numel;c2++){

  offset=c2*elsize;

  fscanf(input," %d %d %d", &eldat[offset], &eldat[offset+1],
          &eldat[offset+2]);

  eldat[offset+3] = (remflag == 1)? rind++ : -1;


/* ********************************************************************
   for each element
   eldat[offset]=element number
   eldat[offset+1]=material property set number
   eldat[offset+2]=number of nodes
   eldat[offset+3]=element density index (-1 if no remodelling)
   ********************************************************************   */

  fprintf(output,"\nElement Number %d degrees of freedom\n", c2+1);
  fprintf(output,"local node, global node, xdof, ydof, zdof\n\n");

  eldof= eldat + offset + (maxnodes+4);

  eldmy = 0;
  netdof=0;
    for(c3=0;c3<eldat[offset+2];c3++){

      fscanf(input," %d", &eldat[offset+c3+4]);

      dmy=3*(eldat[offset+c3+4]-1); /* index to nodal point dof */

      if(eltyp/10 != 2)eldof[eldmy++]=dofptr[dmy];
      eldof[eldmy++]=dofptr[dmy+1];
      eldof[eldmy++]=dofptr[dmy+2];

    }  /* for(c3... */

/* knock out degrees of freedom which
            correspond to repeated nodes */

// canceldofs(&eldat[offset+4],eldof,eltyp,eldat[offset+2]);

   eldmy = 0;
     for(c3=0;c3<eldat[offset+2];c3++){
     fprintf(output," %5d %5d ",c3, eldat[offset+c3+4]);
     if(eltyp/10 != 2){
        fprintf(output,"%5d %5d %5d\n",
               eldof[eldmy],eldof[eldmy+1],eldof[eldmy+2]);
        eldmy += 3;}
     else {
         fprintf(output,"%5d %5d\n",eldof[eldmy],eldof[eldmy+1]);
        eldmy += 2;}
	 } /* for(c3... */

/* adjust matrix profile to account for this element */

    colheight(eldmy,eldof,colptr);


  } /* each element */


} /* loop through element groups */


/* *******************************************
   Read in number of material property sets.
      If the element is to be remodelled, the elastic modulus
      in its property set must be the modulus for volumetric
      density equal to one.

   *******************************************    */

fscanf(input," %d", &nmatp);

/* *********************************************
   get memory for material property information
   *********************************************    */

fprintf(output,"\n\n Material Property Sets:\n\n");

matlsize=3*nmatp;

//matptr= calloc(matlsize, sizeof((double)0));
matptr= new double[matlsize];
if(matptr == NULL)printf("material data allocation failed (main)\n");

/* **************************************
   read in material property information
   **************************************    */

for(c=0;c<nmatp;c++){
fscanf(input," %d", &mtype);
if(mtype == 2)fscanf(input," %d %lf %lf %lf",&c2, &e, &nu, &thic);
if(mtype == 2)fprintf(output,
"\n Set number= %d (%dD) E = %lf Nu =%lf Thickness=%lf\n",c2,mtype,e,nu,thic);

if(mtype == 3)fscanf(input," %d %lf %lf",&c2, &e, &nu);
if(mtype == 3)fprintf(output,
"\n Set number= %d (%dD) E = %lf Nu =%lf\n",c2,mtype,e,nu);


dmy=3*(c2-1);
matptr[dmy]=e;
matptr[dmy+1]=nu;
if(mtype == 2)matptr[dmy+2]=thic;
}  /* for(c=0... */

/* ***************************************
   get memory for volumetric density and rate info
   *************************************** */

   //phiptr=calloc(numrel, sizeof((double)0)); /* actual gamma in iterations */
   phiptr=new double[numrel]();
   if(phiptr == NULL)printf("phi allocation failed (main)\n");

   //rateptr=calloc(numrel, sizeof((double)0)); /* rate of change */
   rateptr=new double[numrel]();
   if(rateptr == NULL)printf("rate allocation failed (main)\n");

   //relvol=calloc(numrel,sizeof((double)0)); /* element volumes */
   relvol=new double[numrel]();
   if(relvol == NULL)printf("element volume allocation failed (main)\n");

/* print out number of remodelling elements */

fprintf(output,"number of remodelling elements = %d\n",numrel);

/* ************************************
   read in initial density distribution
   ************************************  */

   for(c=0;c<numrel;c++)
        fscanf(input," %lf",phiptr+c);


/* *****************************************
   read in loading information:
       for each case,
       create the load vector and store it.
   ***************************************** */

//alpha = calloc(nlcase,sizeof((double)0));
   alpha=new double[nlcase]();
if(alpha == NULL)printf("alpha allocation failed\n");


fprintf(output,"\n\nLoad Cases:\n");

for(c=0;c<nlcase;c++){

/* ****************************
   get memory for loading case
   ****************************     */

//loadptr= calloc(ndoftot, sizeof((double)0));
loadptr = new double[ndoftot]();
if(loadptr == NULL)printf("load allocation failed (main)\n");

fscanf(input," %d %d %lf", &ncase, &nloads, &alpha[c]);
fprintf(output,"\n load case %d has %d nodal loads\n", ncase, nloads);
fprintf(output, "with a remodeling weight of %lf\n", alpha[c]);
fprintf(output,"\n node    direction    value\n");

for(c2=0;c2<nloads;c2++){
    fscanf(input," %d %d %lf", &lnode,&ldof,&lmag);
    netdof=dofptr[3*(lnode-1)+ldof];
    loadptr[netdof]= lmag;
    fprintf(output," %5d %5d %lf\n", lnode,ldof,lmag);
} /* for (c2... */

    wstatus=fwrite(loadptr,sizeof(double),ndoftot,loadfile);
    delete[] loadptr;
    loadptr=nullptr;
//    free(loadptr);
} /* for c ... */

/* ************************************
   read in remodelling simulation data
   ************************************ */
fscanf(input," %lf %lf"
   ,&modexpnt,&tol);
fscanf(input,"%d",&nsizes);

//breakstep=calloc(nsizes,sizeof((int)0));
breakstep=new int[nsizes]();

//stepsiz=calloc(nsizes,sizeof((double)0));
stepsiz=new double[nsizes]();

for(c=0;c<nsizes;c++){
fscanf(input,"%d %lf",&breakstep[c],&stepsiz[c]);
} /* for(c=0... */

fprintf(output, "simulation data \n");
fprintf(output,"modulus exponent = %lf\n",modexpnt);

/* read in measured Z (vertical) displacements */
for(c=0;c<ntnodes;c++){

fscanf(input,"%lf",&mdisp);
//printf("%d %lf \n",dofptr[c*3+2],mdisp);
netdof=dofptr[c*3+2];
mdisptr[netdof]=mdisp;

}

/* read in measured Y(horizontal) displacements */
for(c=0;c<ntnodes;c++){
	fscanf(input,"%lf",&mdisp);
	netdof=dofptr[c*3+1];
	mdisptr[netdof]=mdisp;}

/* ****************************************************
   calculate addresses of diagonal elements in finite element matrix
   ************************************************  */

  diagtrans(colptr,ndoftot);

fprintf(output, "\nDiagonal Addresses:\n");
fprintf(output, "\nDOF:  Address: Minimum Row: \n");

for(c=0;c<=ndoftot;c++){
          r = colptr[c]+c+1-colptr[c+1];
          fprintf(output, "%d %d %d\n",c,colptr[c],r);  }

/* *****************************************
   allocate memory for the stiffness matrix
   *****************************************     */

  matsize= colptr[ndoftot];

  //loadptr= calloc((ndoftot+1)*nlcase, sizeof((double)0));
  loadptr=new double[(ndoftot+1)*nlcase]();
if(loadptr == NULL)printf("load allocation failed (main)\n");

  //workptr= calloc(ndoftot+1, sizeof((double)0));
  workptr= new double[ndoftot+1]();
if(workptr == NULL)printf("diagonal allocation failed (main)\n");

/* print out overall matrix data */

fprintf(output,"\ntotal degrees of freedom = %d\n",ndoftot);
fprintf(output,"\ntotal matrix size = %d\n",matsize);

/*
prnum=4;
m_set_procs(prnum);
*/
tinput=clock();
tchange=tinput-tstart;
cpuinp=tchange/CLOCKS_PER_SEC;
printf("setup cpu time was %lf seconds\n",cpuinp);
fprintf(output,"setup cpu time was %lf seconds\n",cpuinp);

/* $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$

   main loop for remodelling iterations

   $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$  */
doneflag=0;

for(nts=0;;nts++){

/* set time step size */

for(c=0;c<nsizes;c++){
if(nts>breakstep[c])dtime=stepsiz[c];
netime += stepsiz[c];}

  //stifptr = calloc(matsize, sizeof((double)0));
  stifptr= new double[matsize]();
if(stifptr == NULL)printf("stiffness matrix allocation failed (main)\n");


/* *****************************
   loop through element data
     to assemble overall matrix
   *****************************   */

eldstart=0;

printf(" starting assembly\n");

for(c=0;c<nelgps;c++){

/* **********************************
   get memory for element group data
   **********************************   */

  eldat=elarry[c*2];

  numel=eldat[0];
  eltyp=eldat[1];
  maxnodes=eldat[2];
  remflag=eldat[3];

   if(eltyp == 3)elsize= 4 + maxnodes*4;
   if(eltyp/10 == 2)elsize= 4 + maxnodes*3;

   memelem = numel*elsize;

  eldat= elarry[c*2 + 1];

	fflush (stdout);
	fflush (stderr);

/* parallel code
 m_fork(elcalc,eltyp,numel,maxnodes,elsize,eldat);
do{
tst=1;
for(ct=0;ct<prnum;ct++)tst *= ((eldone[ct] == 0)? 0:1);
}
while(tst == 0);
*/

/* serial code */
elcalc(eltyp,numel,maxnodes,elsize,eldat,dofptr,stifptr);

   } /* for (c=... */

/* *******************************

   solve for the displacements

   *******************************    */

printf(" starting solution\n");
fflush(stdout);

/* ******************************
   get matrix blocking info
   ******************************** */
  blockalloc(colptr,ndoftot,output);


/* triangularize the stiffness matrix */

solstat=plinsolv(stifptr,loadptr,colptr,ndoftot,workptr,1,output);
printf("solstat = %d\n",solstat);

rewind(loadfile);

/* solve for displacements for the selected load case */

for(c=0;c<nlcase;c++){

/* read in the force vector */

rstatus=fread(loadptr+c*(ndoftot+1),sizeof(double),ndoftot,loadfile);
if(rstatus != ndoftot){
	printf("force vector read failed (main)\n");
	fflush (stdout);}

solstat=plinsolv(stifptr,loadptr+c*(ndoftot+1),colptr,ndoftot,workptr,3,output);
} /* for c... */

/* **********************************************************************
calculate the average strain energy density
summed overthe load cases
for each remodelling element
and the time stepping matrix
 ************************************************************************/

for(c=0;c<nelgps;c++){

/* calculate element stiffness matrices and incremental matrix */
/* **********************************
   get memory for element group data
   **********************************   */

eldat=elarry[c*2];

  numel=eldat[0];
  eltyp=eldat[1];
  maxnodes=eldat[2];
  remflag=eldat[3];

   if(eltyp == 3)elsize= 4 + maxnodes*4;
   if(eltyp/10 == 2)elsize= 4 + maxnodes*3;

   memelem = numel*elsize;

eldat=elarry[c*2 + 1];

  if(remflag == 1){

/***********************************************************
   calculate element stiffness matrices, strain energy density
 ***********************************************************/

  printf("calculating element forces\n");
  fflush(stdout);


elforce(eltyp,numel,maxnodes,elsize,eldat,dofptr);
  } /* if(remflag...*/
  } /* loop through element groups */

fprintf(output,"\n\n    volumetric densities \n\n");
gamnorm=0.0;
dgamnorm=0.0;
ratenorm=0.0;
oblnorm=0.0;

netact=0;
for(c=0;c<numrel;c++){

rateptr[c] *= (-modexpnt/phiptr[c]);
phiptr[c] += rateptr[c]*dtime;

   ratenorm += rateptr[c]*rateptr[c];

}
ratenorm = sqrt(ratenorm/numrel);
printf("rate norm: %lf\n", ratenorm);

for(c=0;c<numrel;c++)
	printf("%d\t%lf\t%lf\n",c,phiptr[c],rateptr[c]);
for(c=0;c<numrel;c++)
	fprintf(output,"%d\t%lf\t%lf\n",c,phiptr[c],rateptr[c]);

for(c2=0;c2<ntnodes;c2++){
   ux=uy=uz=0.;
   dmy=c2*3;
   if((df=dofptr[dmy]) != 0)ux=loadptr[df];
   if((df=dofptr[dmy+1]) != 0)uy=loadptr[df];
   if((df=dofptr[dmy+2]) != 0)uz=loadptr[df];
   fprintf(output,"%8d, %20.15lf, %20.15lf, %20.15lf\n",c2+1,ux,uy,uz);
   printf("%8d, %20.15lf, %20.15lf, %20.15lf\n",c2+1,ux,uy,uz);

}

/* $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
   end of overall remodelling simulation loop
   $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$ */
if(ratenorm<tol)break;
} /* for loop */

/* end of program   */

}

/****************************************************************************
*****************************************************************************/

void diagtrans (int mcolptr[],int ndoftot)
{
int c,h,hlast;
maxcolht=0;
mcolptr[1]=0;
hlast=mcolptr[2];
mcolptr[2]=1;

for(c=3;c<ndoftot+2;c++){
  maxcolht = (maxcolht >hlast) ? maxcolht: hlast;
  h=mcolptr[c];
  mcolptr[c]=mcolptr[c-1]+hlast+1;
  hlast=h;
  }
}
/****************************************************************************
*****************************************************************************/

void colheight (int edof,int eldof[],int gbldof[])
{
int c,min,colht,dmy;
/* find smallest dof */
  min=10000000;
for(c=0;c<edof;c++){
  if(eldof[c]>0){ min= (eldof[c]<min) ? eldof[c] : min;
  }
}
/* update column data */
for(c=0;c<edof;c++){
  if((dmy=eldof[c])>0){
    colht=dmy-min;
    gbldof[dmy] = (gbldof[dmy] > colht) ? gbldof[dmy] : colht;
  }

}
}
/****************************************************************************
*****************************************************************************/

/* **************************************************
   routine to calculate element strain energy density
   ************************************************** */

double elstend(int eldof[],double elstf[],double disp[],int neldof,double volume,double work[])
//int neldof,*eldof;
//double *elstf,*disp,volume,*work;
{
int c, c2,dind,elind;
double net;

net=0.;

for(c=0;c<neldof;c++){

work[c]=0.;

   if(eldof[c] != 0){

      for(c2=0;c2<neldof;c2++){

/* ********************
   element matrix index
   ******************** */

          elind= (c>c2)? (c*(c+1)/2 + c2): (c2*(c2+1)/2 + c);
          dind= eldof[c2];  /*  displacement index */
          if(eldof[c2] !=0)work[c] += elstf[elind]*disp[dind];
        } /* for(c2 ... */

      }  /* if(eldof[c]... */

    }  /* for(c...  */


for(c=0;c<neldof;c++){

   if(eldof[c] != 0){

       dind=eldof[c];

       net += work[c]*disp[dind];

       }  /* if(eldof[c]... */

    }  /* for(c...  */

   net /= 2.0*volume;

return(net);

}

/****************************************************************************
*****************************************************************************/

/* **************************************************
   routine to calculate element matrix - total displacement dot products
   ************************************************** */

void eldisdot(int eldof[],double elstf[],double disp[],int neldof,double work[])
//int neldof,*eldof;
//double *elstf,*disp,*work;
{
int c, c2,dind,elind;
double net;

for(c=0;c<neldof;c++){

work[c]=0.;

   if(eldof[c] != 0){

      for(c2=0;c2<neldof;c2++){

/* ********************
   element matrix index
   ******************** */

          elind= (c>c2)? (c*(c+1)/2 + c2): (c2*(c2+1)/2 + c);
          dind= eldof[c2];  /*  displacement index */
          if(eldof[c2] !=0)work[c] += elstf[elind]*disp[dind];

        } /* for(c2 ... */

      }  /* if(eldof[c]... */

    }  /* for(c...  */

return;

} /* end of routine */

/****************************************************************************
*****************************************************************************/

void elcalc(int eltyp,int numel,int maxnodes,int elsize,int eldat[],int dofptr[],double stifptr[])
//int eltyp,numel,maxnodes,elsize,*eldat;
{
int maxdel,memsize,*eldof;
double *elstf,*elstdm,*elnpc,volume;
int c2,c3,itype,nodnum,offset;
int remind,id,estat;
double elnpc2[9][2],elnpc3[21][3],elstdm2[9][4],elstdm3[21][6];
/* subroutine to do parallel calculation of element matrices */
int dfind;
int eNodDF[63];
double *s;
//extern double *matptr,*gamptr,*coorptr,*relvol;
//extern int *colptr,ndoftot;
//extern double modexpnt,transexpnt;
//extern FILE *output;

/* ******************************************
   get memory for element stiffness matrices
   ******************************************   */

  if(eltyp/10 == 2){
      maxdel=maxnodes*2;
      memsize=maxdel*(maxdel+1)/2 + 6*maxdel;

      //elstf= calloc(memsize, sizeof((double)0));
      elstf= new double[memsize]();

if(elstf == NULL){
/*   m_lock(); */
   printf("element stiffness matrix allocation failed (elcalc)\n");
/*   m_unlock(); */ }

      elstdm=elstf + maxdel*(maxdel+1)/2;
      elnpc=elstdm+4*maxdel; }

  if(eltyp == 3){
      maxdel=maxnodes*3;
      memsize=maxdel*(maxdel+1)/2 + 9*maxdel;
      //elstf= calloc(memsize, sizeof((double)0));
      elstf= new double[memsize]();

if(elstf == NULL){
 /*         m_lock(); */
          printf("element stiffness matrix allocation failed (elcalc)\n");
 /*          m_unlock(); */ }

      elstdm=elstf + maxdel*(maxdel+1)/2;
      elnpc=elstdm+6*maxdel; }

  /* *************************
   for each element
   eldat[offset]=element number
   eldat[offset+1]=material property set number
   eldat[offset+2]=number of nodes
   eldat[offset+3]=remodelling index
   *************************   */

/* parallel code
for(;;){

c2=m_next();

if(c2 >= numel){
   free(elstf);

id = m_get_myid();

   eldone[id]=1;

   return;     }
*/

/* serial code */
  for(c2=0;c2<numel;c2++){
  offset=c2*elsize;
  eldof= eldat + offset + (maxnodes+4);

   remind= eldat[offset+3];



	//set up material data to pass to the element threads
	  int matnumber=eldat[offset+1];
	  double matpass[4];
	  int elemdof=0;
	  if (eltyp/10==2){
     elemdof=2*eldat[offset+2];
	  s=new double[elemdof*(elemdof+1)/2];
	  matpass[0]=matptr[(matnumber-1)*4];
	  matpass[1]=matptr[(matnumber-1)*4+1];
	  matpass[2]=matptr[(matnumber-1)*4+2];
	  matpass[3]=matptr[(matnumber-1)*4+3];
	  }
	  if(eltyp==3){
	   elemdof=3*eldat[offset+2];
	   s=new double[elemdof*(elemdof+1)/2];
	   matpass[0]=matptr[(matnumber-1)*4];
	   matpass[1]=matptr[(matnumber-1)*4+1];
	   matpass[2]=matptr[(matnumber-1)*4+2];
	  }
	  int denind=eldat[offset+3];


	  double gammar= denind>=0 ? pow(phiptr[denind],modexpnt) : -1;




  if(eltyp == 3){
	  dfind=0;
  for(c3=0;c3<eldat[offset+2];c3++){
	  nodnum=eldat[offset+c3+4];
     elnpc3[c3][0]=coorptr[3*(nodnum-1)];
     elnpc3[c3][1]=coorptr[3*(nodnum-1)+1];
     elnpc3[c3][2]=coorptr[3*(nodnum-1)+2];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+0];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+1];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+2];}

  estat=threedsolid(eldat[offset],eldat[offset+2],3,
         matpass,elnpc3,s,output,&volume,gammar,modexpnt);
/* m_lock(); */
  if(estat != 0)printf("negative jacobian in element # %d\n",eldat[offset]);
  addel(eNodDF,s,stifptr,colptr,ndoftot,eldat[offset+2]*3);
/* m_unlock(); */
  }  /* if(eltyp == 3... */

  if(eltyp/10 == 2){
	     dfind=0;
  for(c3=0;c3<eldat[offset+2];c3++){
	  nodnum=eldat[offset+c3+4];
     elnpc2[c3][0]=coorptr[3*(nodnum-1)+1];  //y, z cords
     elnpc2[c3][1]=coorptr[3*(nodnum-1)+2];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+1];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+2];}

  itype=eltyp-20;

  estat=twodsolid(eldat[offset],eldat[offset+2],itype,3,
       matpass,elnpc2,s,output,&volume,gammar,modexpnt);
/* m_lock(); */
  if(estat != 0)printf("negative jacobian in element # %d\n",eldat[offset]);
  addel(eNodDF,s,stifptr,colptr,ndoftot,eldat[offset+2]*2);
/* m_unlock(); */
  }  /* if(eltyp/10 == 2... */

   if (remind>=0)relvol[remind]=volume;

  }  /* endless for loop  */

  delete[] elstf;
  elstf=nullptr;
 //  free(elstf);

} /* routine end */


/****************************************************************************
****************************************************************************/

/* routine to do parallel dot products to get strain energy density
   and element nodal point force info  */


void elforce(int eltyp,int numel,int maxnodes,int elsize,int eldat[],int dofptr[])
//int eltyp,numel,maxnodes,elsize,*eldat;
{
int maxdel,memsize,*eldof,offset;
double *elstf,*elstdm,*elnpc,volume;
int c2,c3,itype,nodnum,solstat,rind,elfoff,id,index,dfind;
extern int nlcase;

double *s;
extern double *gamptr,transexpnt;
//extern int *dofptr;
int eNodDF[63];
double elnpc2[9][2],elnpc3[21][3];
double elstdm2[9][4],elstdm3[21][6];


/* ******************************************
   get memory for element stiffness matrices
   ******************************************   */

  if(eltyp/10 == 2){
      maxdel=maxnodes*2;
      memsize=maxdel*(maxdel+1)/2 + 6*maxdel;
      //elstf= calloc(memsize, sizeof((double)0));
      elstf= new double[memsize];

      if(elstf == NULL){
	/* m_lock(); */
        printf("element stiffness matrix allocation failed (elforce)\n");
        /* m_unlock(); */ }

      elstdm=elstf + maxdel*(maxdel+1)/2;
      elnpc=elstdm+4*maxdel; }

  if(eltyp == 3){
      maxdel=maxnodes*3;
      memsize=maxdel*(maxdel+1)/2 + 9*maxdel;
      //elstf= calloc(memsize, sizeof((double)0));
      elstf= new double[memsize]();
      if(elstf == NULL){
        /* m_lock(); */
        printf("element stiffness matrix allocation failed (elforce)\n");
	/* m_unlock(); */}

      elstdm=elstf + maxdel*(maxdel+1)/2;
      elnpc=elstdm+6*maxdel; }

/* *************************
   for each element
   eldat[offset]=element number
   eldat[offset+1]=material property set number
   eldat[offset+2]=number of nodes
   eldat[offset+3]=remodelling index
   *************************   */
/* parallel code
for(;;){

c2=m_next();

if(c2 >= numel){

  free(elstf);
id = m_get_myid();

   eldone[id]=1;
 m_lock();
printf("elforce proc = %d\n",id);
fflush(stdout);
 m_unlock();

  return;
}
  parallel code */

/* serial code */

  for(c2=0;c2<numel;c2++){
  offset=c2*elsize;
  eldof= eldat + offset + (maxnodes+4);

  if(eldat[offset+3]>=0){

		//set up material data to pass to the element threads
		  int matnumber=eldat[offset+1];
		  double matpass[4];
		  int elemdof=0;
		  if (eltyp/10==2){
	     elemdof=2*eldat[offset+2];
		  s=new double[elemdof*(elemdof+1)/2]();
		  matpass[0]=matptr[(matnumber-1)*4];
		  matpass[1]=matptr[(matnumber-1)*4+1];
		  matpass[2]=matptr[(matnumber-1)*4+2];
		  matpass[3]=matptr[(matnumber-1)*4+3];
		  }
		  if(eltyp==3){
		   elemdof=3*eldat[offset+2];
		   s=new double[elemdof*(elemdof+1)/2]();
		   matpass[0]=matptr[(matnumber-1)*4];
		   matpass[1]=matptr[(matnumber-1)*4+1];
		   matpass[2]=matptr[(matnumber-1)*4+2];
		  }
		  int denind=eldat[offset+3];

		  double gammar= denind>=0 ? pow(phiptr[denind],modexpnt) : -1;

  if(eltyp == 3){
	  dfind=0;
  for(c3=0;c3<eldat[offset+2];c3++){
     nodnum=eldat[offset+c3+4];
     elnpc3[c3][0]=coorptr[3*(nodnum-1)];
     elnpc3[c3][1]=coorptr[3*(nodnum-1)+1];
     elnpc3[c3][2]=coorptr[3*(nodnum-1)+2];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+0];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+1];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+2];}

  threedsolid(eldat[offset],eldat[offset+2],3,
         matpass,elnpc3,s,output,&volume,gammar,modexpnt);

  }  /* if(eltyp == 3... */

  if(eltyp/10 == 2){
	  dfind=0;
  for(c3=0;c3<eldat[offset+2];c3++){
     nodnum=eldat[offset+c3+4];
     elnpc2[c3][0]=coorptr[3*(nodnum-1)+1];
     elnpc2[c3][1]=coorptr[3*(nodnum-1)+2];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+1];
	eNodDF[dfind++]=dofptr[(nodnum-1)*3+2];}

  itype=eltyp-20;

  twodsolid(eldat[offset],eldat[offset+2],itype,3,
       matpass,elnpc2,s,output,&volume,gammar,modexpnt);


  }  /* if(eltyp/10 == 2... */


/* take dot products with calculated displacements
   to get strain energy density and rate of change */

   rind=eldat[offset+3];

   rateptr[rind]=0.0;

for(c3=0;c3<nlcase;c3++){

  index=c3*(ndoftot+1);

  rateptr[rind] += alpha[c3]*
           (-elstend(eNodDF,s,&loadptr[index],maxdel,volume,elnpc)
		   + elstend(eNodDF,s,mdisptr,maxdel,volume,elnpc));

/* elfoff = rind*netmaxdel + c3*netmaxdel*numrel;
  eldisdot(eldof,elstf,&loadptr[index],maxdel,elnodf+elfoff); */

/* printf("rind= %d,rateptr[rind]= %lf,eldiag[rind]= %lf\n",
        rind,rateptr[rind],eldiag[rind]); */

}
fprintf(output,"%d: %lf\n",rind, rateptr[rind]);
  } /* if(eldat[offset+3]>=0 ...  */

  }  /* for(;;... */

  delete[] s;
  s=nullptr;
//  free(elstf);

} /* end of routine */

 /*********************

  c routine to cancel out element degrees of freedom
    which correspond to repeated nodes

 ***************************/

 int canceldofs(int *nodes, int *dofs, int eltyp, int nnodes)
 {
 int c,c2,c3,dpn;

 dpn = (eltyp/10 == 2) ? 2:3;

 for(c=0;c<(nnodes-1); c++){

    for(c2=c+1;c2<nnodes;c2++){

       if(nodes[c2]==nodes[c]){

           for(c3=0;c3<dpn;c3++)dofs[c2*dpn+c3]=0;
                               } /* if */
                               } /* for */
                             } /* for */
 return(0);
 }
/* end of file */
