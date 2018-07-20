
#### SIMULATION DATASET
set.seed(66)
library(bayesm)
nvar=4                          ## number of coefficients
nlgt=100                        ## number of cross-sectional units
nrounds=10				      ## number of observations per unit
rounds=1:10				## rounds index
noffer=11						## number of possible offers
nz=1                           	## number of regressors in mixing distribution


# c(entire pie)*sigma(share of the pie A offers)
## share of the pie
Sigma=c(0, .1, .2, .3, .4, .5, .6, .7, .8, .9, 1)
## size of the pie
c=10
## set social reference point (can also be estimated)
gamma=1/2

## set hyper-parameters
## B=ZDelta + U  
Z=matrix(c(rep(1,nlgt)),nrow=nlgt,ncol=nz)
true_coefs=c(2, -0.2, -1, -3) 
## mean of random effects
Delta=matrix(true_coefs,nrow=nz,ncol=nvar)
## vcov
Vbeta=diag(c(0.5, 0.4, 0.3, 0.2))


## simulate data
ldata=NULL
for (i in 1:nlgt) 
{
  beta=as.vector(t(Delta)%*%Z[i,]+(t(chol(Vbeta))%*%rnorm(nvar)))  
  b=exp(beta[1])
  taualpha=exp(beta[2])
  taubeta=exp(beta[3])
  tau1=exp(beta[4])
  
  # utility of B if accept
  # initialize the utilities
  UBAcc=UAAcc=rep(0, noffer)
  UBAcc[Sigma<=gamma]=c*(Sigma[Sigma<=gamma]-(b/2)*((Sigma[Sigma<=gamma]-gamma)^2)) 
  UBAcc[Sigma>gamma]=c*Sigma[Sigma>gamma]
  #utility of A/B if reject
 UARej= UBRej=rep(0, 11)
  
  #utility of A if B accepts
  UAAcc[Sigma>=gamma]=c*((1-Sigma[Sigma>=gamma])-(b/2)*(((1-Sigma[Sigma>=gamma])-gamma)^2)) 
  UAAcc[Sigma<gamma]=c*(1-Sigma[Sigma<gamma])
  
  #initialize probability matrices
  PbB=matrix(rep(0, noffer*nrounds), ncol=noffer)
  ExUAAcc=matrix(rep(0, noffer*nrounds), ncol=noffer)
  PbA=matrix(rep(0, noffer*nrounds), ncol=noffer)
  
  # compute probability matrices for the probability of B to accept, expected value of A in case B accepts and the probability of A to make an offer of sigma
  PbB=exp((taubeta*(1+tau1*(rounds-1)))%*%t(UBAcc))/(1+exp((taubeta*(1+tau1*(rounds-1)))%*%t(UBAcc)))
  #A's expected utility if A offers X to B
  ExUAAcc=t(UAAcc*t(PbB))
  #Pb of A to offer X
  PbA=(exp(taualpha*(1+tau1*(rounds-1))*ExUAAcc))/rowSums(exp((taualpha*(1+tau1*(rounds-1)))*ExUAAcc))
  X=matrix(rep(0, noffer*nrounds), ncol=noffer)
  for (j in 1:nrounds)
  X[j,]= rmultinom(1, 1, PbA[j,])
  y=rep(0, nrounds)
  unif=runif(nrounds,0,1)
  for (j in 1:nrounds)
    y[j]= ifelse(unif[j]<PbB[j,][X[j,]==1],1,0)
  ldata[[i]]=list(beta=beta, y=y, X=X)
}


true_betas=NULL
for (i in 1:nlgt)
  true_betas=rbind(true_betas, ldata[[i]]$beta)
colMeans(true_betas)


## the likelihood function
erc.lk<- function (beta, X, y)
	{ 	
		b=exp(beta[1])
		taualpha=exp(beta[2])
		taubeta=exp(beta[3])
		tau1=exp(beta[4])

# utility of B if accept
# initialize the utilities
UBAcc=UAAcc=rep(0, noffer)
UBAcc[Sigma<=gamma]=c*(Sigma[Sigma<=gamma]-(b/2)*((Sigma[Sigma<=gamma]-gamma)^2)) 
UBAcc[Sigma>gamma]=c*Sigma[Sigma>gamma]
#utility of A/ B if reject
UARejUBRej=rep(0, noffer)

#utility of A if B accepts
UAAcc[Sigma>=gamma]=c*((1-Sigma[Sigma>=gamma])-(b/2)*(((1-Sigma[Sigma>=gamma])-gamma)^2)) 
UAAcc[Sigma<gamma]=c*(1-Sigma[Sigma<gamma])

#initialize probability matrices
PbB=matrix(rep(0, noffer*nrounds), ncol=noffer)
ExUAAcc=matrix(rep(0, noffer*nrounds), ncol=noffer)
PbA=matrix(rep(0, noffer*nrounds), ncol=noffer)
# compute probability matrices for the probability of B to accept, expected value of A in case B accepts and the probability of A to make an offer of sigma
PbB=exp((taubeta*(1+tau1*(rounds-1)))%*%t(UBAcc))/(1+exp((taubeta*(1+tau1*(rounds-1)))%*%t(UBAcc)))

#create the nlgt*nroundss matrix necessary to compute the pooled likelihood
PbBpooled=matrix(rep(t(PbB),nlgt), ncol=ncol(PbB), byrow=TRUE)

#A's expected utility if A offers X to B
ExUAAcc=t(UAAcc*t(PbB))
#Pb of A to offer X
PbA=(exp(taualpha*(1+tau1*(rounds-1))*ExUAAcc))/rowSums(exp((taualpha*(1+tau1*(rounds-1)))*ExUAAcc))
PbApooled=matrix(rep(t(PbA),nlgt), ncol=ncol(PbA), byrow=TRUE)

## probability of either reject or accept, computed by taking into consideration the response of player B
PbBRpooled=PbBpooled
y1=matrix(rep(y, noffer), ncol=noffer)
PbBRpooled[y1==0&X==1]=1-PbBpooled[y1==0&X==1]

logl=sum(log(rowSums(PbApooled*PbBRpooled*X)))
return(logl)
}


#### Bayesian function to estimate b, taualpha, taubeta, tau1 parameters, for the pooled model 
################################
myERCrwMetrop<-function (Data, Prior, Mcmc) 
{
#define the likelihood function
 	X=Data$X
	y=Data$y
  nvar = 4
   ### prior
    betabar= Prior$betabar
    A = Prior$A
      ## scaling parameter, critical to the success of the RW algorithm. 
      ## MCMC parameters
            sbeta = Mcmc$sbeta
            keep = Mcmc$keep
            R = Mcmc$R
    ### initializes the matrices to store the parameter estmates, llike and the var-cov matrix
    betadraw = matrix(double(floor(R/keep) * nvar), ncol = nvar)
    llike = double(floor(R/keep))
    # I start with parameter values at 0. Tried also with parameter values at MLE estimates, results don't chanage
    beta = c(rep(0, nvar))
    betaz = c(rep(0, nvar))
    betabar=c(rep(0, nvar))
	# this is the candidate covariance. I start with the identity matrix and update it every 500 iteration
    cov = diag(nvar)
    candcov = chol2inv(chol(cov))
    root = chol(candcov)
    rooti = backsolve(root, diag(nvar))
    priorcov = chol2inv(chol(A))
   rootp = chol(priorcov)
   rootpi = backsolve(rootp, diag(nvar))   
    itime = proc.time()[3]
    cat("MCMC Iteration (est time to end - min)", fill = TRUE)
    #fsh()
    # the llike of the current draw, evaluated at the starting values in the MCMC, here at beta=c(0, 0, 0, 0). 
    oldllike= erc.lk(beta,X, y)
    # the posterior again evaluated at the starting values. this is needed to create the alpha of the first draw of the MCMC
    oldlpost = -0.5*as.vector(t(rootpi)%*%(beta-betabar))%*%as.vector(t(rootpi)%*%(beta-betabar)) 
   # start of the MH algorithm
   naccept=0
    for (rep in 1:R) {
    	# candidate vector
          betac= beta+sbeta*t(root)%*%rnorm(length(beta))     
            ## the logl evaluated at the candidate vector
            cllike = erc.lk(betac, X, y)
            clpost = -0.5*as.vector(t(rootpi)%*%(betac-betabar))%*%as.vector(t(rootpi)%*%(betac-betabar))      
        ldiff = cllike+clpost-oldllike-oldlpost
        # compute alpha, the acceptance probability of the MH algorithm
        alpha = min(1, exp(ldiff))
        if (alpha == "NaN") 
               alpha = -1
        #generate an uniform draw  
        if (alpha < 1) {
            unif = runif(1)
        } else {
            unif = 0
        }
        #if unif is less than alpha, the candidate vector is accepted      
        if (unif <= alpha) {
            beta = betac
            oldllike = cllike
            oldlpost = clpost
            naccept = naccept + 1
        }
        
        # variables monitoring the speed of the chain 
        if (rep%%100 == 0) {
            ctime = proc.time()[3]
            timetoend = ((ctime - itime)/rep) * (R - rep)
            cat(" ", rep, " (", round(timetoend/60, 1), ")",fill = TRUE)
            #fsh()
        }
    # store the draws of beta and likelihood values
        if (rep%%keep == 0) {
            mkeep = rep/keep
            betadraw[mkeep, ] = beta
            llike[mkeep] = oldllike
        }      
    }   
  # varibale that monitor the speed of the chain
    ctime = proc.time()[3]
    cat("  Total Time Elapsed: ", round((ctime - itime)/60, 2), 
        "\n")
    return(list(betadraw = betadraw, llike = llike, acceptr = naccept/R, sbeta=sbeta))
}   

#######################################################
# define the dataset 
### values for prior and mcmc
X=ldata[[1]]$X
y=c(ldata[[1]]$y)
for (i in 2:nlgt)
{
	X=rbind(X, ldata[[i]]$X)
	y=c(y, ldata[[i]]$y)
	}

Data=list(X=X,y=y)

#define the MCMC parameters
R=10000
burnin=5000
## i'm keeping every 10th draw. helps reducing the autocorrelation
keep=1
Mcmc=list(R=R,keep=keep, sbeta=0.1)
#define the prior mean and varcov matrix     
Prior=list(A=0.01*diag(nvar),betabar=c(rep(-0.01, nvar)))

#run the MCMC     
out_agg=myERCrwMetrop(Data=Data,Prior=Prior,Mcmc=Mcmc)

########### plot the posterior log-likelihood
matplot(out_agg$llike[burnin:R/keep], type="l", xlab="Iterations/10", ylab=" ", main="Posterior Log-Likelihood")
#### bayes factor
logBF=logMargDenNR(out_agg$llike[burnin:(R/keep)])
## sumarize the values of the draws of the parameter estimates, with a burnin period to be decied after looking at the logl graph
out_agg$acceptr
cat("Summary of beta draws",fill=TRUE)
summary(out_agg$betadraw[burnin:R/keep,])
beta=colMeans(true_betas)
cat(" Betadraws obtained from random-walk chain ",fill=TRUE)
     mat=apply(out_agg$betadraw,2,quantile,probs=c(.01,.05,.5,.95,.99))
     mat=rbind(beta,mat); rownames(mat)[1]="beta"; print(mat)

     matplot(out_agg$betadraw,type="l",col=c(1:length(beta)))
     for (i in 1:length(beta)){
     abline(beta[i],0,col=i)
     }

     par(mfrow=c(2,2))
     for (i in 1:nvar){
     hist(out_agg$betadraw[,i])
     }

     par(mfrow=c(2,2))
     for (i in 1:nvar){
     acf(out_agg$betadraw[,i])
     }

## the likelihood for one individual: run this line by line
## choice matrix for A player's offer over 10 rounds of the game
X=ldata[[1]]$X
## B player's accept/reject decision over the 10 rounds of the game
y=ldata[[1]]$y
## parameters
beta=ldata[[1]]$beta
erc.lk<- function (beta, X, y)
     { 	
       b=exp(beta[1])
       taualpha=exp(beta[2])
       taubeta=exp(beta[3])
       tau1=exp(beta[4])
       
       # utility of B if accept
       # initialize the utilities
       UBAcc=UAAcc=rep(0, noffer)
       UBAcc[Sigma<=gamma]=c*(Sigma[Sigma<=gamma]-(b/2)*((Sigma[Sigma<=gamma]-gamma)^2)) 
       UBAcc[Sigma>gamma]=c*Sigma[Sigma>gamma]
       #utility of A/ B if reject
       UARejUBRej=rep(0, noffer)
       
       #utility of A if B accepts
       UAAcc[Sigma>=gamma]=c*((1-Sigma[Sigma>=gamma])-(b/2)*(((1-Sigma[Sigma>=gamma])-gamma)^2)) 
       UAAcc[Sigma<gamma]=c*(1-Sigma[Sigma<gamma])
       
       #initialize probability matrices
       PbB=matrix(rep(0, noffer*nrounds), ncol=noffer)
       ExUAAcc=matrix(rep(0, noffer*nrounds), ncol=noffer)
       PbA=matrix(rep(0, noffer*nrounds), ncol=noffer)
       # compute probability matrices for the probability of B to accept, expected value of A in case B accepts and the probability of A to make an offer of sigma
       PbB=exp((taubeta*(1+tau1*(rounds-1)))%*%t(UBAcc))/(1+exp((taubeta*(1+tau1*(rounds-1)))%*%t(UBAcc)))
       #A's expected utility if A offers X to B
       ExUAAcc=t(UAAcc*t(PbB))
       #Pb of A to offer X
       PbA=(exp(taualpha*(1+tau1*(rounds-1))*ExUAAcc))/rowSums(exp((taualpha*(1+tau1*(rounds-1)))*ExUAAcc))
       ## probability of either reject or accept, computed by taking into consideration the response of player B
       PbBR=PbB
       y1=matrix(rep(y, noffer), ncol=noffer)
       PbBR[X==1&y1==0]=1-PbB[X==1&y1==0]
       
       logl=sum(log(rowSums(PbA*PbBR*X)))
       return(logl)
     }
     
