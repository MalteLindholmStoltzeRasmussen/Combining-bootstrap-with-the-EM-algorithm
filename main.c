/* This program makes it possible to obtain confidence regions for estimates of parameters in phase-type distributions. The program is carried out in C by modification of an already existing program (see Marita Olsson, The empht-programme, Relatório técnico, Department of Mathematics, Chalmers University of Technology, and Göteborg University, Sweden, 1998). For more details see chapter 6 in the attached pdf. It is allowed to use this program, provided that authors name, Malte Lindholm Stoltze Rasmussen is expressly stated as source. */


/* including libraries */
#include<stdio.h>
#include<stdlib.h>
#include<math.h>

/* declaration of global variables */
double *obs, *obsS, *weight;
double  SumOfWeights, SumOfWeightsS, cv, prec;
int  NoOfObs, Ra, sim_k, iT,*pilegal, **Tlegal, IV, OW, RI;

/*  functions for allocation of memory */
double *v_alloc(int n)
{
  double *v;
  v=(double *) calloc(n,sizeof(double));
  if(v==NULL) {
    fprintf(stderr,"could not allocate memory");
    exit(1);
  }
  return v;
}

int *int_v_alloc(int n)
{
  int *v;
  v=(int *) calloc(n,sizeof(int));
  if(v==NULL) {
    fprintf(stderr,"could not allocate memory");
    exit(1);
  }
  return v;
}

double **m_alloc(int n, int k)
{
  int i;
  double **mat;
  mat=(double **) calloc(n,sizeof(double *));
  if(mat == NULL) {
    fprintf(stderr,"could not allocate memory");
    exit(1);
  }
  for(i=0; i<n; i++) {
    mat[i]=(double *) calloc(k,sizeof(double));
    if(mat[i] == NULL) {
      fprintf(stderr,"could not allocate memory");
      exit(1);
    }
  }
  return mat;
}

int **int_m_alloc(int n, int k)
{
  int i, **mat;
  mat=(int **) calloc(n,sizeof(int *));
  if(mat == NULL) {
    fprintf(stderr,"could not allocate memory");
    exit(1);
  }
  for(i=0; i<n; i++) {
    mat[i]=(int *) calloc(k,sizeof(int));
    if(mat[i] == NULL) {
      fprintf(stderr,"could not allocate memory");
      exit(1);
    }
  }
  return mat;
}

double ***m3_alloc(int n, int k, int v)
{
  int i,j;
  double ***mat;
  mat=(double ***) calloc(n,sizeof(double **));
  if(mat == NULL) {
    fprintf(stderr,"could not allocate memory");
    exit(1);
  }
  for(i=0; i<n; i++) {
    mat[i]=(double **) calloc(k,sizeof(double *));
    if(mat[i] == NULL) {
      fprintf(stderr,"could not allocate memory");
      exit(1);
    }
    for(j=0; j<k; j++) {
      mat[i][j]=(double *) calloc(v,sizeof(double));
      if(mat[i][j] == NULL) {
	fprintf(stderr,"could not allocate memory");
	exit(1);
      }
    }
  }
  return mat;
}

/* subroutines for initiatization */
void init_vector(double *vector, int NoOfElements)
{
  int i;
  for(i=0; i < NoOfElements; i++)
    vector[i] = 0.0;
}

void init_matrix(double **matrix, int dim1, int dim2)
{
  int i, j;

  for (i=0; i<dim1; i++)
    for(j=0; j<dim2; j++)
      matrix[i][j] = 0.0;
}

void init_3dimmatrix(double ***matrix, int dim1, int dim2, int dim3)
{
  int i, j, k;

  for (i=0; i<dim1; i++) 
    for(j=0; j<dim2; j++) 
      for(k=0; k<dim3; k++)
	matrix[i][j][k] = 0;
}

void free_matrix(double **matrix, int dim1)
{
  int i;

  for (i=0; i<dim1; i++)
    free(matrix[i]); 
  free(matrix);
}

void free_integermatrix(int **matrix, int dim1)
{
  int i;

  for (i=0; i<dim1; i++)
    free(matrix[i]);
  free(matrix);
}

void free_3dimmatrix(double ***matrix, int dim1, int dim2)
{
  int i;

  for (i=0; i<dim1; i++) 
    free_matrix(matrix[i],dim2);
  free(matrix);
}

/* Runge Kutta procedure for calculation of matrix exponentials */
void a_rungekutta(int p, double *avector, double **ka, double dt, double h, 
		  double **T)
{
  int i,j;
  double eps, h2, sum;

  i=dt/h;
  h2=dt/(i+1);
  init_matrix(ka, 4, p);

  for (eps=0; eps<=dt-h2/2; eps += h2) {
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[j][i]*avector[j];
      ka[0][i] = h2*sum;
    }
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[j][i]*(avector[j]+ka[0][j]/2);
      ka[1][i] = h2*sum;
    }
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[j][i]*(avector[j]+ka[1][j]/2);
      ka[2][i] = h2*sum;
    }
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[j][i]*(avector[j]+ka[2][j]);
      ka[3][i] = h2*sum;
    }

    for (i=0; i < p; i++) 
      avector[i] += (ka[0][i]+2*ka[1][i]+2*ka[2][i]+ka[3][i])/6;
  }
}

void rungekutta(int p, double *avector, double *gvector, double *bvector, 
		double **cmatrix, double dt, double h, double **T, double *t, 
		double **ka, double **kg, double **kb, double ***kc)
{
  int i, j, k, m;
  double eps, h2, sum;

  i = dt/h;
  h2 = dt/(i+1);
  init_matrix(ka, 4, p);
  init_matrix(kb, 4, p);
  init_3dimmatrix(kc, 4, p, p);
  if (kg != NULL) 
    init_matrix(kg, 4, p);

  for (eps = 0; eps <= dt-h2/2; eps += h2) {
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[j][i]*avector[j];
      ka[0][i] = h2*sum;
    }
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[j][i]*(avector[j]+ka[0][j]/2);
      ka[1][i] = h2*sum;
    }
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[j][i]*(avector[j]+ka[1][j]/2);
      ka[2][i] = h2*sum;
    }
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[j][i]*(avector[j]+ka[2][j]);
      ka[3][i] = h2*sum;
    }
    
    if (gvector != NULL) {
      for (i=0; i < p; i++) 
	kg[0][i] = h2*avector[i];
      for (i=0; i < p; i++) 
	kg[1][i] = h2*(avector[i]+ka[0][i]/2);
      for (i=0; i < p; i++) 
	kg[2][i] = h2*(avector[i]+ka[1][i]/2);
      for (i=0; i < p; i++) 
	kg[3][i] = h2*(avector[i]+ka[2][i]);
      for (i=0; i < p; i++) 
      gvector[i] += (kg[0][i]+2*kg[1][i]+2*kg[2][i]+kg[3][i])/6;
    }
    
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[i][j]*bvector[j];
      kb[0][i] = h2*sum;
    }
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[i][j]*(bvector[j]+kb[0][j]/2);
      kb[1][i] = h2*sum;
    }
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[i][j]*(bvector[j]+kb[1][j]/2);
      kb[2][i] = h2*sum;
    }
    for (i=0; i < p; i++) {
      sum=0;
      for (j=0; j < p; j++)
        sum += T[i][j]*(bvector[j]+kb[2][j]);
      kb[3][i] = h2*sum;
    }
   
    for (m=0; m < p; m++)
      for (i=0; i < p; i++) {
        sum=t[m]*avector[i];
        for (j=0; j < p; j++)
          sum += T[m][j]*cmatrix[j][i];
        kc[0][m][i] = h2*sum;
      }
    for (m=0; m < p; m++)
      for (i=0; i < p; i++) {
        sum=t[m]*(avector[i]+ka[0][i]/2);
        for (j=0; j < p; j++)
          sum += T[m][j]*(cmatrix[j][i]+kc[0][j][i]/2);
        kc[1][m][i] = h2*sum;
      }
    for (m=0; m < p; m++)
      for (i=0; i < p; i++) {
        sum=t[m]*(avector[i]+ka[1][i]/2);
        for (j=0; j < p; j++)
          sum += T[m][j]*(cmatrix[j][i]+kc[1][j][i]/2);
        kc[2][m][i] = h2*sum;
      }
    for (m=0; m < p; m++)
      for (i=0; i < p; i++) {
        sum=t[m]*(avector[i]+ka[2][i]);
        for (j=0; j < p; j++)
          sum += T[m][j]*(cmatrix[j][i]+kc[2][j][i]);
        kc[3][m][i] = h2*sum;
      }
    
    for (i=0; i < p; i++) {
      avector[i] += (ka[0][i]+2*ka[1][i]+2*ka[2][i]+ka[3][i])/6;
      bvector[i] += (kb[0][i]+2*kb[1][i]+2*kb[2][i]+kb[3][i])/6;
      for (j=0; j < p; j++)
        cmatrix[i][j] +=(kc[0][i][j]+2*kc[1][i][j]+2*kc[2][i][j]+kc[3][i][j])/6;
    }
  }
} 

/* subroutine for displaying estimated parameter values */
void show_pi_T(int p, double *pi, double **T, double *t)
{
  int i, j;
  
  for (i=0; i < p; i++) {
    printf("\n%lf    ", pi[i]);
    for (j=0; j < p; j++)
      printf("%lf ", T[i][j]);
    printf("   %lf",t[i]);
  }
  printf("\n");
}

/* default step length */
double set_steplength(int p, double **T)
{    
  int i;
  double h;

  h= -0.1/T[0][0];
  for (i=1; i < p; i++)
    if (h > -0.1/T[i][i])
      h = -0.1/T[i][i];
  return(h);
}

/* subroutine for importing and observations */
void input_sample(int NoOfInput[3])
{
  double Obs, Weight;
  FILE *utfil, *infil;

    Weight=1;
    infil=fopen("unweighted", "r");
    utfil=fopen("sample", "w");
    fscanf(infil, "%le", &Obs);
    while (Obs >= 0) {
      NoOfInput[1]++;
      fprintf(utfil, "%e %e \n", Obs, Weight);
      fscanf(infil, "%le", &Obs);
    }
    fprintf(utfil, "-1");
    fclose(infil);
    fclose(utfil);

}

/*  assigning observations to vectors */
void assign_vectors(int No)
{
  int i;
  FILE *infil;
  
  infil=fopen("sample", "r");
   for(i=0; i < No; i++) {
    fscanf(infil, "%le %le", &obs[i], &weight[i]);
    SumOfWeights += weight[i];
  }
  fclose(infil);
}

/* sorting observations and identification of
 *  unique observations */
int sort_observations(int size, double *vec1, double *vec2)
{
  int i,j, tempweight, newsize;
  double tempobs;

  newsize=size;
  for (i=0; i < size-1; i++)
    for (j=i+1; j < size; j++)
      if (vec1[i] > vec1[j]) {
        tempobs = vec1[i];
        vec1[i] = vec1[j];
        vec1[j] = tempobs;
        tempweight = vec2[i];
        vec2[i] = vec2[j];
        vec2[j] = tempweight;
      }
  for (i=size-2; i >= 0; i--)
    if (vec1[i] == vec1[i+1]) {
      vec2[i] += vec2[i+1];
      newsize--;
      for(j=i+1; j < newsize; j++) {
        vec1[j] = vec1[j+1];
        vec2[j] = vec2[j+1];
      }
    }
  return (newsize);
}

/*  preparatory procedure */
int AskForInput(int NoOfInput[3])
{
  int input, sampletype;

      sampletype = 1;
      input_sample(NoOfInput);
      obs = v_alloc(NoOfInput[1]);
      obsS = v_alloc(NoOfInput[1]);
      weight = v_alloc(NoOfInput[1]);
      assign_vectors(NoOfInput[1]);
      NoOfObs = sort_observations(NoOfInput[1], obs, weight);
      printf("Total number of observations = %d\n", (int) SumOfWeights);

  return(sampletype);
}

/* random initiatization -  not used
 *  when simulating */
double random1()
{
  double r;

  r=rand();
  r /= ((double) RAND_MAX);
  r *= 0.9;
  r += 0.1;
  return(r);
}

void randomphase(int p, double *pi, double **T, double *exitvector, 
		 int *pilegal, int **Tlegal)
{
  int i, j;
  double r, sum, scalefactor;

    scalefactor=obs[(NoOfObs-1)/2];

  sum=0;
  for (i=0; i < p; i++)
    if (pilegal[i] == 1) {
      pi[i]=random1();
      sum += pi[i];
    }
  for (i=0; i < p; i++)
    pi[i]=pi[i]/sum;
  for (i=0; i < p; i++)
    for (j=0; j < p; j++)
      if ((i != j) && (Tlegal[i][j] == 1)) {
        T[i][j]=random1();
        T[i][i] -= T[i][j];
      }
  for (i=0; i < p; i++)
    if (Tlegal[i][i] == 1) {
      r=random1();
      T[i][i] -= r;
      exitvector[i]=r;
    }
  for (i=0; i < p; i++) {
    exitvector[i] = exitvector[i] * p/ scalefactor;
    for (j=0; j < p; j++)
      T[i][j] = T[i][j] * p / scalefactor;
  }
}

/*  selection of structure:
 *  Random initiation used in modern selection
 *  When simulating saved parameter values are imported */
void selectstructure(int p, double *pi, double **T, double *t, int *pilegal,
		     int **Tlegal)
{
  int i, j, structure;
  FILE *infil;

    if (IV == 2) {
        structure = 7;
    } else {
        structure = 1;
    }

  switch(structure) {
  case 1:
    for (i=0; i < p; i++) {
      pilegal[i]=1;
      for (j=0; j < p; j++)
	Tlegal[i][j]=1;
    }
    break;
  case 7:
    infil=fopen("phases", "r");
    for (i=0; i < p; i++) {
      fscanf(infil, "%le", &pi[i]);
      for (j=0; j < p; j++)
	fscanf(infil, "%le", &T[i][j]);
    }
    fclose(infil);
    break;
  }

  if (structure < 7) {
    printf("\n Phase-type structure:");
    for (i=0; i < p; i++) {
      printf("\n%d     ", pilegal[i]);
      for (j=0; j < p; j++)
        printf("%d ", Tlegal[i][j]);
    }
    printf("\nRandom initiation - enter an integer (at random):");
    scanf("%d",&RI);
    srand(RI);
    printf("\n");
    randomphase(p, pi, T, t, pilegal, Tlegal);
  }
  else 
    for (i=0; i < p; i++) 
      for (j=0; j < p; j++) 
	t[i] -= T[i][j];
}

/* EM algorithm */
void EMstep(int p, double h, double *pi, double **T, double *t, double 
            *gvector, double *avector, double *bvector, double **cmatrix, 
            double *Bmean, double *Zmean, double **Nmean, double **kg, 
            double **ka, double **kb, double ***kc)
{
  int i, j, k;
  double pitimesb, dt;
  init_vector(Bmean, p);
  init_vector(Zmean, p);
  init_matrix(Nmean, p, p+1);

  if (NoOfObs > 0) {
    for (i=0; i < p; i++) {
      avector[i]=pi[i];
      bvector[i]=t[i];
    }
    init_matrix(cmatrix, p, p);  
    dt = obs[0];
    for (k=0; k < NoOfObs; k++) {
      if (dt > 0)
	rungekutta(p, avector, NULL, bvector, cmatrix, dt, h, T, t, ka, NULL,
		   kb, kc);
      pitimesb=0;
      for (i=0; i < p; i++)
	pitimesb += pi[i]*bvector[i];
      for (i=0; i < p; i++) {
	Bmean[i] += pi[i]*bvector[i]*weight[k]/pitimesb;
	Nmean[i][p] += avector[i]*t[i]*weight[k]/pitimesb;
	Zmean[i] += cmatrix[i][i]*weight[k]/pitimesb;
	for (j=0; j < p; j++) 
	  Nmean[i][j] += T[i][j]*cmatrix[j][i]*weight[k]/pitimesb;
      }
      dt=obs[k+1]-obs[k];
    }
  }

    /*   identification of change in estimated
     *  parameter values since last iteration */
    cv = 0;
    for (i=0; i < p; i++) {
        if (cv < fabs(pi[i]-Bmean[i] / SumOfWeights))
        cv = fabs(pi[i]-Bmean[i] / SumOfWeights);

        if (cv < fabs(t[i] - Nmean[i][p] / Zmean[i]))
            t[i] = fabs(Nmean[i][p] / Zmean[i]);

        for (j=0; j < p; j++){
            if (cv < fabs(T[i][j] - Nmean[i][j] / Zmean[i]))
                cv = fabs(T[i][j] - Nmean[i][j] / Zmean[i]);
            }
    }

    for (i=0; i < p; i++) {
    pi[i] = Bmean[i] / (SumOfWeights);
    if (pi[i] < 0)
      pi[i] = 0;
    t[i] = Nmean[i][p] / Zmean[i];
    if (t[i] < 0)
      t[i] = 0;
    T[i][i] = -t[i];
    for (j=0; j < p; j++) 
      if (i!=j) {
	T[i][j] = Nmean[i][j] / Zmean[i];
	if (T[i][j] < 0)
	  T[i][j] = 0;
	T[i][i] -= T[i][j];
      } 
  }

}

/* computation of log-likelihood */
void compute_loglikelihood(double h, int p, double *pi, double **T, double *t, 
			   int stepindicator, double *avector, double **ka, 
			   double **a_left, int k, int NoOfEMsteps)
{
  int i, j;
  double loglikelihood,atimesexit, dt;
  
  if (stepindicator == 1)
    h = set_steplength(p, T);
  loglikelihood = 0;
  
  if (NoOfObs > 0) {
    for (i=0; i < p; i++)
      avector[i] = pi[i];
    dt = obs[0];
    for (i=0; i < NoOfObs; i++) {
      atimesexit = 0.0;
      if (dt > 0)
	a_rungekutta(p, avector, ka, dt, h, T);
      for (j=0; j < p; j++)
	atimesexit += avector[j] * t[j];
      loglikelihood += weight[i] * log(atimesexit);  
      dt = obs[i+1]-obs[i];
    }
    /* calculation and exportation of information criterias
     *  for each simulation */
      if (k==NoOfEMsteps) {
          FILE *utfil;
        if (OW == 1){
            utfil = fopen("loglik", "w");
        } else {
            utfil = fopen("loglik", "a");
        }
            fprintf(utfil, "%lf phases: %d iterations: %d seed: %d AIC: %f BIC: %f\n",
                          loglikelihood,p,NoOfEMsteps,RI,
                          2*(p*p+p-1)-2*loglikelihood,
                          log(SumOfWeights)*(p*p+p-1)-2*loglikelihood);
            fclose(utfil);
      }
  }

  printf("Log-likelihood = %lf \n", loglikelihood);
}

/* exportation of estimated parameter values
 *  when using model selection */
void SavePhases(int p, double *pi, double **T)
{ 
  int i,j;
  FILE *utfil;

  utfil=fopen("phases", "w");
  for (i=0; i < p; i++) { 
    fprintf(utfil, "\n%e   ", pi[i]);
    for (j=0; j < p; j++)
      fprintf(utfil, "%e ", T[i][j]);
  }
  fclose(utfil);
}

/* exportation of the estimated parameter values
 *  for each simulation */
void SavePhasesT(int p, double **T) {
    int i,j;
    FILE *utfil;


    utfil=fopen("phasesT", "a");
    for (i=0; i < p; i++) {
        for (j=0; j< p; j++) {
            fprintf(utfil, "%e ", T[i][j]);
        }
    }
    fprintf(utfil, "\n");
    fclose(utfil);
}


void SavePhasesPi(int p, double *pi) {
    int i;
    FILE *utfil;

    utfil=fopen("phasesPi", "a");
    for (i=0; i < p; i++) {
        fprintf(utfil, "%e ", pi[i]);

    }
    fprintf(utfil, "\n");
    fclose(utfil);
}

/* main subroutine for the EM algorithm */
void EMiterate(int NoOfEMsteps, int p, double *pi, double **T, double *t,
	       double *gvector, double *avector, double *bvector, 
               double **cmatrix, double *Bmean, double *Zmean, double **Nmean, 
	       double **kg, double **ka, double **kb, double ***kc, 
               double *ett)
{
  int i, j, k,l, stepindicator, stepchoice, tempSim, tempEM;
  double RKstep;

    stepindicator = 1;


    if (IV == 2){
        tempSim = 1;
        NoOfEMsteps *= sim_k;

        /* Random seed in order to recreate the simulations */
        printf("\nRandom initiation - enter an integer (at random):");
        scanf("%d",&iT);
        srand(iT);
        printf("\n");

        /* Resample procedure */
        init_vector(weight,NoOfObs);
        for(i=0; i < SumOfWeights; i++) {
            Ra=rand()%NoOfObs;
                weight[Ra]  += 1;
        }

        FILE *utfil;
        utfil=fopen("phasesT", "w");
        fclose(utfil);
        utfil=fopen("phasesPi", "w");
        fclose(utfil);
        utfil=fopen("Iterations", "w");
        fclose(utfil);
    }

    for (k=1; k <= NoOfEMsteps; k++) {
        RKstep = set_steplength(p, T);
        EMstep(p, RKstep, pi, T, t, NULL, avector, bvector, cmatrix, Bmean,
               Zmean, Nmean, NULL, ka, kb, kc);
        if (IV == 2) {
            /* displaying Number of iterations, simulations
             * estimated parameter values and the biggest
             * absolute change since last iteration */
            tempEM = (k % ((NoOfEMsteps / sim_k)+1)+sim_k-1);
            printf("\nEM(%d)",tempEM);
            printf("\nSim(%d)",tempSim);
            printf("\nPrecision(%f)",cv);
            show_pi_T(p, pi, T, t);

            /* procedure for when the preciseness
             * in the convergence is achieved */
            if (cv <  prec){
              FILE *utfil;
              utfil=fopen("Iterations", "a");

              /* exporting the number of iterations
               * used for convergence for each simulation */
              fprintf(utfil, "%d\n", tempEM);
              fclose(utfil);
              k = tempSim*(NoOfEMsteps / sim_k);
            }

            /*  exporting converged values of the simulation */
            if ((k % (NoOfEMsteps / sim_k)) == 0) {
              if (cv >  prec){
                FILE *utfil;
                utfil=fopen("Iterations", "a");

                /* exporting the number of iterations
                 * used for convergence if upper bound reached */

                fprintf(utfil, "%d\n", (NoOfEMsteps / sim_k));
                fclose(utfil);
              }
                SavePhasesPi(p, pi);
                SavePhasesT(p, T);

                /*  Randomization */
                iT = rand();
                srand(iT);

                /* reload the parameter values
                 *  for initiatization of the next simulation */
                selectstructure(p, pi, T, t, pilegal, Tlegal);
                init_vector(weight, NoOfObs);

                /* resample algorithm */
                for (i = 0; i < SumOfWeights; i++) {
                    Ra = rand() % NoOfObs;
                    weight[Ra] += 1;
                }

            }
        }

    /*  exportation. only used in modern selection */
    if ((k < 6) || ( (k % 25)==0 || k==NoOfEMsteps )) {
              if (IV == 1) {
                  SavePhases(p, pi, T);
                  printf("\nEM(%d)",k);
                  show_pi_T(p, pi, T, t);
                  compute_loglikelihood(RKstep, p, pi, T, t, stepindicator, avector, ka,
                                        NULL,k,NoOfEMsteps);


              } else {
                  if ((k % (NoOfEMsteps / sim_k)) == 0) {
                      tempSim += 1;
                  }


              }
    }
  }
}

main() 
{
  int i, j, sampletype, fitting, p,  NoOfEMsteps, choice, newp; 
  int *pilegal, **Tlegal, NoOfInput[3]={0, 0, 0}, NoToSave; 
  double  *pi, **T, *t, *avector, *gvector, *bvector, **cmatrix; 
  double *Bmean, *Zmean, **Nmean, **ka, **kg, **kb, ***kc, dig;
  double **a_left, **g_left, **b_left, ***c_left, *ett; 
  
  sampletype=0;
  fitting=1;
  NoOfObs=0;
  SumOfWeights=0;

  /* start menu */
    printf("Press 1 for initialization\n");
    printf("Press 2 for simulations\n");
    scanf("%d", &IV);
    if (IV == 2) {
        printf("Enter number of simulations\n");
        scanf("%d", &sim_k);

      printf("Enter level of precision\n");
      scanf("%lf", &dig);
      prec = pow(10,-dig);
    }
if (IV == 1){
    printf("Overwrite loglik-file?\n");
    printf("Press 1 for yes\n");
    printf("Press 2 for no\n");
    scanf("%d", &OW);
}
  sampletype = AskForInput(NoOfInput);
  printf("\nNumber of phases of the PH-distribution to be fitted, (p): ");
  scanf("%d", &p); 
 
  pi=v_alloc(p); T=m_alloc(p, p); t=v_alloc(p);
  pilegal=int_v_alloc(p); Tlegal=int_m_alloc(p, p);
  avector=v_alloc(p);  bvector=v_alloc(p); cmatrix=m_alloc(p, p);  
  Bmean=v_alloc(p); Zmean=v_alloc(p); Nmean=m_alloc(p, p+1); 
  ka=m_alloc(4, p);  kb=m_alloc(4, p); kc=m3_alloc(4, p, p); 
  if (sampletype==2) {
    ett = v_alloc(p);
    for(i=0; i < p; i++)
      ett[i] = 1;
  }

  selectstructure(p, pi, T, t, pilegal, Tlegal);
  show_pi_T(p, pi, T, t);

  while (fitting == 1) {    
    printf("\nNumber of EM-iterations: ");
    scanf("%d", &NoOfEMsteps);
    EMiterate(NoOfEMsteps, p, pi, T, t, gvector, avector, bvector, cmatrix, 
      Bmean, Zmean, Nmean, kg, ka, kb, kc, ett);

      if (IV == 1) {
          SavePhases(p, pi, T);
      }

      fitting = 0;
      }
  
  free(pi); free_matrix(T, p);  free(t); free(pilegal);
  free_integermatrix(Tlegal,p); 
  free(avector); free(bvector); free_matrix(cmatrix,p); 
  free_matrix(ka, 4);  free_matrix(kb, 4);  
  free_3dimmatrix(kc, 4, p);  free(Bmean); free(Zmean);
  free_matrix(Nmean, p);  

  if(sampletype == 2)
    free(ett);
}
