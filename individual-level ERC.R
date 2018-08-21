## Alina Ferecatu
## August 2018

## Use the simulated data from the aggregate estimation

##### The likelihood function #######
erc.lk<- function (beta, X, y)
{  
  b=exp(beta[1])
  taualpha=exp(beta[2])
  taubeta=exp(beta[3])
  tau1=exp(beta[4])
  # c(entire pie)*sigma(share of the pie A offers)
  Sigma=c(0, .1, .2, .3, .4, .5, .6, .7, .8, .9, 1)
  c=10
  
  # utility of B if accept
  # initialize the utilities
  UBAcc=UAAcc=rep(0, noffer)
  UBAcc[Sigma<=1/2]=c*(Sigma[Sigma<=1/2]-(b/2)*((Sigma[Sigma<=1/2]-1/2)^2)) 
  UBAcc[Sigma>1/2]=c*Sigma[Sigma>1/2]
  
  #utility of B if reject
  UBRej=UAAcc=rep(0, noffer)
  #utility of A if B accepts
  UAAcc[Sigma>=1/2]=c*((1-Sigma[Sigma>=1/2])-(b/2)*(((1-Sigma[Sigma>=1/2])-1/2)^2)) 
  UAAcc[Sigma<1/2]=c*(1-Sigma[Sigma<1/2])
  
  #initialize probability matrices
  PbB=matrix(rep(0, noffer*nround), ncol=noffer)
  ExUAAcc=matrix(rep(0, noffer*nround), ncol=noffer)
  PbA=matrix(rep(0, noffer*nround), ncol=noffer)
  
  # compute probability matrices for the probability of B to accept, expected value of A in case B accepts and the probability of A to make an offer of sigma  
  PbB=exp((taubeta*(1+tau1*(round-1)))%*%t(UBAcc))/(1+exp((taubeta*(1+tau1*(round-1)))%*%t(UBAcc)))
  #A's expected utility if A offers X to B
  ExUAAcc=t(UAAcc*t(PbB))
  #Pb of A to offer X
  PbA=(exp(taualpha*(1+tau1*(round-1))*ExUAAcc))/rowSums(exp((taualpha*(1+tau1*(round-1)))*ExUAAcc))
  
  ## probability of either reject or accept, computed by taking into consideration the response of player B
  PbBR=PbB
  X1=matrix(rep(X, noffer), ncol=noffer)
  PbBR[X1==0&y==1]=1-PbB[X1==0&y==1]

  logl=sum(log(rowSums(PbA*PbBR*y)))
  return(logl)
}

######## hierarchical Bayes estimation ################################
myhierERC<-function (Data, Prior, Mcmc) 
{
    # X data for each individual
    lgtdata = Data$lgtdata
    nlgt = length(lgtdata)
    ## random effects for each individual
    Z = Data$Z
    nz = ncol(Z)
    nvar = length(beta)
    # prior
    nu = Prior$nu
    V = Prior$V
    ADelta = Prior$ADelta
    Deltabar = Prior$Deltabar
	## MCMC chain variables
	sbeta=Mcmc$sbeta
	keep = Mcmc$keep
	burnin = Mcmc$burnin
	R = Mcmc$R
	
    Vbetadraw = matrix(double(floor(R/keep) * nvar * nvar), ncol = nvar * nvar)
    ## saved draws for the respondent-level coefficients
    betadraw = array(double(floor(R/keep) * nlgt * nvar), dim = c(nlgt, nvar, floor(R/keep)))
    ## draws of regression coefficients in the random effects model.
    Deltadraw = matrix(double(floor(R/keep) * nvar * nz), ncol = nvar * nz)
    ## current draws of the variables are reffered to as "old" variables
    oldbetas = matrix(rep(-0.1,nlgt * nvar), ncol = nvar)  
    oldVbeta = 10*diag(nvar) 
    oldVbetai =  chol2inv(chol(oldVbeta)) 
    oldDelta = matrix(double(nvar * nz), ncol = nvar)
    ## betad and betan are the default and new draws of beta used in the MH algorithm
    betad = array(0, dim = c(nvar))
    betan = array(0, dim = c(nvar))
    reject = array(0, dim = c(R/keep))
    llike = array(0, dim = c(R/keep))  
    itime = proc.time()[3]
    cat("MCMC Iteration (est time to end - min)", fill = TRUE)

	## Start the MCMC chain 
    for (j in 1:R) {
        rej = 0
        logl = 0    
        sV=sbeta*oldVbeta
  		root=t(chol(sV))      
       for (i in 1:nlgt) {
            ### the current vector of parameters
            betad = oldbetas[i, ]    
	    ## candidate vector of parameters
            betan= betad+root%*%rnorm(nvar)   		
            ## the logl evaluated at the old and new values
            lognew = erc.lk(betan, lgtdata[[i]]$X, lgtdata[[i]]$y)
            logold = erc.lk(betad, lgtdata[[i]]$X, lgtdata[[i]]$y)
            ### the contribution of density from the distribution of heterogeneity
            logknew = -0.5 * (t(betan) - Z[i, ] %*% oldDelta) %*%oldVbetai %*% (betan - t(Z[i, ] %*% oldDelta))
            logkold = -0.5 * (t(betad) - Z[i, ] %*% oldDelta) %*%oldVbetai %*% (betad - t(Z[i, ] %*% oldDelta))
            ## compute alpha, the acceptance pb for the MH algorithm
            alpha = exp(lognew + logknew - logold - logkold)
            if (alpha == "NaN") 
               alpha = -1
            ## a uniform draw u is generated
            u = runif(n = 1, min = 0, max = 1)
            ## if u is less than alpha, the new vector of coefficients is accepted
            if (u < alpha) {
                oldbetas[i, ] = betan
                logl = logl + lognew
            }
            else {
                logl = logl + logold
                rej = rej + 1
            }
        }
        ## second step of the algorithm: random effects coefficients  
        ## bayesian multiple regression: rmultireg bayesm package
        out = rmultireg(oldbetas, Z, Deltabar, ADelta, nu, V)
        ## stores the coefficiets
        oldDelta = out$B
        ### stores the var-cov 
        oldVbeta = out$Sigma
        oldVbetai = chol2inv(chol(oldVbeta))
        # variables monitoring the speed of the chain 
        if ((j%%100) == 0) {
            ctime = proc.time()[3]
            timetoend = ((ctime - itime)/j) * (R - j)
            cat(" ", j, " (", round(timetoend/60, 1), ")", fill = TRUE)
            #fsh()
        }
        # store the draws of beta, delta, rejection rates and likelihood values
        mkeep = j/keep
        if (mkeep * keep == (floor(mkeep) * keep)) {
            Deltadraw[mkeep, ] = as.vector(oldDelta)
            Vbetadraw[mkeep, ] = as.vector(oldVbeta)
            betadraw[, , mkeep] = oldbetas
            llike[mkeep] = logl
            reject[mkeep] = rej/nlgt
        }
    }
 
    ctime = proc.time()[3]
    cat(" Total Time Elapsed: ", round((ctime - itime)/60, 2), 
        fill = TRUE)
    attributes(betadraw)$class = c("bayesm.hcoef")
    attributes(Deltadraw)$class = c("bayesm.mat", "mcmc")
    attributes(Deltadraw)$mcpar = c(1, R, keep)
    attributes(Vbetadraw)$class = c("bayesm.var", "bayesm.mat",  "mcmc")
    ### the variables to return 
    attributes(Vbetadraw)$mcpar = c(1, R, keep)
    return(list(betadraw = betadraw, Vbetadraw = Vbetadraw, Deltadraw = Deltadraw, llike = llike, reject = reject))
}

### values for prior and mcmc
noffer=11
nround=10
nvar=4                    ## number of variables
nlgt=length(ldata)             ## number of cross-sectional units
nz=1                      ## number of regressors in mixing distribution
nu=nvar+2*(length(ldata[[1]]$Response)) #nvar+3
R=10000
## i'm keeping every 10th draw for averages and plots
keep=1
burnin=5000

## the random effects, a vector of ones
Z=as.matrix(rep(1, nhh))

## run the MCMC chain
out=myhierERC(Data=list(lgtdata=ldata, Z=Z),Mcmc=list(R=R, keep=keep, burnin=burnin, sbeta=.3), 
	      Prior=list( nu=nu, V=nu * diag(rep(0.1, nvar)), Deltabar=matrix(rep(0, nz * nvar), ncol = nvar), ADelta=0.01*diag(nz)))
						
## sumarize the effects of demographics
cat("Summary of Delta draws",fill=TRUE)
Delta=out$Deltadraw[burnin:(R/keep),]
attributes(Delta)$class = c("bayesm.mat", "mcmc")
    attributes(Delta)$mcpar = c(1, ((R/keep)-burnin), keep)
## plot the summary of the random effects, after removing the burin period
plot(Delta)

### sumarize the variance-covariance mattrix of the random effects.
cat("Summary of Vbeta draws",fill=TRUE)
summary(out$Vbetadraw)
summary(out$llike)


