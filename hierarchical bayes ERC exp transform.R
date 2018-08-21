setwd("/Users/alinaferecatu/Dropbox/papers/bargaining HB ERC/data")

## import the dataset in txt format
DatasetRothFull=read.table("DatasetRothFull.txt",header=TRUE)
library(bayesm)
names(DatasetRothFull)
hist(DatasetRothFull$Offer, breaks=10, main="", xlab="Actual offers - the Roth et al. dataset", ylab="Frequency", ylim=c(0,500), xlim=c(0, 10))

## set up a list where the data is organized by individual
## each individual has a set of variables as in the loop below
# group variable: buyer ID
hh=levels(factor(DatasetRothFull$Buyer))
##number of levels needed in the for loops 
nhh=length(hh)
### initialize the list
ldata=NULL


### import the dataset as a list format. 
for (i in 1:nhh) {
#import obs. nr. variable
Seller=as.vector(DatasetRothFull[DatasetRothFull[,1]==hh[i],2])
Round=as.vector(DatasetRothFull[DatasetRothFull[,1]==hh[i],3])
offer=floor(as.vector(DatasetRothFull[DatasetRothFull[,1]==hh[i],4]))
Response=as.vector(DatasetRothFull[DatasetRothFull[,1]==hh[i],5])
country=as.vector(DatasetRothFull[DatasetRothFull[,1]==hh[i],6])
Choice=matrix(double(110), ncol=11)
Pb=matrix(double(110), ncol=11)
ldata[[i]]=list(Seler=Seller,Round=Round, offer=offer,Response=Response, country=country, Choice= Choice, Pb=Pb)
}

#create the choice matrix, the y variable in our model
for(i in 1:nhh)
			{			
			for (k in 1:nrow(ldata[[1]]$Choice))
				{
				for (j in 1:ncol(ldata[[1]]$Choice))
					{ 
			if (ldata[[i]]$offer[k]==j-1) ldata[[i]]$Choice[k,j]=1
				else ldata[[i]]$Choice[k,j]=0
				}
			}
	}
	
#check the dmensionality and shape of the Choice matrix
dim(ldata[[1]]$Choice)
ldata[[20]]$Choice
## for testing the likelihood function
X=ercdata[[1]]$X
y=ercdata[[1]]$y
beta=c(2.23, -0.13,-1.27 , -2.81)
beta=rep(-0.5, nvar)

##### the likelihood function
erc.lk<- function (beta, X, y)
{   
  ## in case we don't want to estimate the fairness parameter for the A players
  ## very hard to do so since we do not have offers higher than 5
  ## here is set at the mean of the fairness parameters for B players for 
  ## MCMC itertaion j-1 at every round, but could be fixed to a specific value
  b=exp(beta[1])
  #bA=exp(mean(oldbetas[,1]))
  taualpha=exp(beta[2])
  taubeta=exp(beta[3])
  tau1=exp(beta[4])
  # c(entire pay)*sigma(share of the pay A offers)
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
  PbB=exp((taubeta*(1+tau1*(ldata[[1]]$Round-1)))%*%t(UBAcc))/(1+exp((taubeta*(1+tau1*(ldata[[1]]$Round-1)))%*%t(UBAcc)))
  #A's expected utility if A offers X to B
  ExUAAcc=t(UAAcc*t(PbB))
  #Pb of A to offer X
  PbA=(exp(taualpha*(1+tau1*(ldata[[1]]$Round-1))*ExUAAcc))/rowSums(exp((taualpha*(1+tau1*(ldata[[1]]$Round-1)))*ExUAAcc))
  
  ## probability of either reject or accept, computed by taking into consideration the response of player B
  PbBR=PbB
  X1=matrix(rep(X, noffer), ncol=noffer)
  PbBR[X1==0&y==1]=1-PbB[X1==0&y==1]

  logl=sum(log(rowSums(PbA*PbBR*y)))
  return(logl)
}
#### hierarchical Bayes function to compute b, taualpha, taubeta, tau1 parameters 
################################

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
	
    ####allocates storage for the draws: saved draws of the var-cov matrix of the random effects cov matrix
    Vbetadraw = matrix(double(floor(R/keep) * nvar * nvar), ncol = nvar * nvar)
   ## saved draws for the respondent-level coefficients
    betadraw = array(double(floor(R/keep) * nlgt * nvar), dim = c(nlgt, nvar, floor(R/keep)))
    ## draws of regression coefficients in the random effects model.
    Deltadraw = matrix(double(floor(R/keep) * nvar * nz), ncol = nvar * nz)
    ## current draws of the variables are reffered to as "old" variables
    oldbetas = matrix(rep(-0.1,nlgt * nvar), ncol = nvar)  
    oldVbeta = 10*diag(nvar) #c(.74, .073, .027,.016)*diag(nvar) 
    ### oldbetai is (Vbeta)-1
    oldVbetai =  chol2inv(chol(oldVbeta)) 
    oldDelta = matrix(double(nvar * nz), ncol = nvar)
    ## betad and betan are the default and new draws of beta used in the MH algorithm
    betad = array(0, dim = c(nvar))
    betan = array(0, dim = c(nvar))
    reject = array(0, dim = c(R/keep))
    llike = array(0, dim = c(R/keep))  
    itime = proc.time()[3]
    cat("MCMC Iteration (est time to end - min)", fill = TRUE)
 
  #########################
	## Start the MCMC chain ##
  ##########################  
    for (j in 1:R) {
        rej = 0
        logl = 0    
        sV=sbeta*oldVbeta
  		root=t(chol(sV))      
       for (i in 1:nlgt) {
        	### the current vector of parameters
            betad = oldbetas[i, ]
	#the candidate vector, obtained by adding a draw from normal distribution with mean at the current draw and var-cov matrix proporational 
  #to the one of the previos draws (updates every 500 iterations)         
            betan= betad+root%*%rnorm(nvar)   		
            ## the logl evaluated at the old and new values
            lognew = erc.lk(betan, lgtdata[[i]]$X, lgtdata[[i]]$y)
            logold = erc.lk(betad, lgtdata[[i]]$X, lgtdata[[i]]$y)
            ### the contribution of density from the distribution of heterogeneity
            logknew = -0.5 * (t(betan) - Z[i, ] %*% oldDelta) %*%oldVbetai %*% (t(t(betan)) - t(Z[i, ] %*% oldDelta))
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
    ### variables that monitor the speed of the chain, write time of completion information on the screen
    ctime = proc.time()[3]
    cat(" Total Time Elapsed: ", round((ctime - itime)/60, 2), 
        fill = TRUE)
    attributes(betadraw)$class = c("bayesm.hcoef")
    attributes(Deltadraw)$class = c("bayesm.mat", "mcmc")
    attributes(Deltadraw)$mcpar = c(1, R, keep)
    attributes(Vbetadraw)$class = c("bayesm.var", "bayesm.mat", 
        "mcmc")
    ### the variables to return 
    attributes(Vbetadraw)$mcpar = c(1, R, keep)
    return(list(betadraw = betadraw, Vbetadraw = Vbetadraw, Deltadraw = Deltadraw, llike = llike, reject = reject))
}

### values for prior and mcmc
noffer=11
nround=10
nvar=4                    ## number of variables
nlgt=length()                      ## number of cross-sectional units
nz=1                      ## number of regressors in mixing distribution
nu=nvar+2*(length(ldata[[1]]$Response)) #nvar+3
R=10000
## i'm keeping every 10th draw for averages and plots
keep=1
burnin=5000

ercdata=NULL
### define the X and Y of the model. 
for (i in 1:nhh) 
{
y=as.matrix(ldata[[i]]$Choice)
X=as.vector(ldata[[i]]$Response)
Buyer=hh[i]
## try sensityvity for starting values at .5 for p
beta=rep(-0.1, nvar)
###Initialize the erc parameters
ercdata[[i]]=list(y=y, X=X, Buyer=Buyer, beta=beta)
}

## the random effects, a vector of ones
Z=as.matrix(rep(1, nhh))

## run the MCMC chain
out=myhierERC(Data=list(lgtdata=ercdata, Z=Z),Mcmc=list(R=R, keep=keep, burnin=burnin, sbeta=.3), Prior=list( nu=nu, V=nu * diag(rep(0.1, nvar)), Deltabar=matrix(rep(0, nz * nvar), ncol = nvar), ADelta=0.01*diag(nz)))
						
## sumarize the effects of demographics
cat("Summary of Delta draws",fill=TRUE)
save(out, file="hberc results v4 indhet.RData")

setwd("/Users/alinaferecatu/Dropbox/papers/bargaining HB ERC/data")
load("hberc results v4 indhet.RData")

Delta=out$Deltadraw[burnin:(R/keep),]
attributes(Delta)$class = c("bayesm.mat", "mcmc")
    attributes(Delta)$mcpar = c(1, ((R/keep)-burnin), keep)
## plot the summary of the random effects, taking into consideration the burin period
plot(Delta)


dim(Delta)
hist(exp(Delta[,4]))
### sumarize the variance-covariance mattrix of the random effects.
cat("Summary of Vbeta draws",fill=TRUE)


summary(out$Vbetadraw)
beta_agg=out_agg$betadraw[burnin:(R/keep),]
beta_ind=out$Deltadraw[burnin:(R/keep),]
par(mfrow=c(2,2))
plot(density(beta_agg[,1]),main=expression(paste("Fairness parameter b")), xlim=c(1, 3), ylim=c(0,7))
lines(density(beta_ind[,1]), lty=2)
legend("topright", legend=c("Agg", "Ind"), lty=1:2)
plot(density(beta_agg[,2]), main=expression(paste("Proposer's strategy parameter ", tau, alpha)), xlim=c(-1, 1.5), ylim=c(0,7)) 
lines(density(beta_ind[,2]), lty=2)
legend("topright", legend=c("Agg", "Ind"), lty=1:2)
plot(density(beta_agg[,3]), main=expression(paste("Responder's strategy parameter ", tau, beta)), xlim=c(-2,-0.5), ylim=c(0,7))
lines(density(beta_ind[,3]), lty=2)
legend("topright", legend=c("Agg", "Ind"), lty=1:2)
plot(density(beta_agg[,4]), main=expression(paste("Experience parameter ", tau, "1")), xlim=c(-4, -1), ylim=c(0,7))
lines(density(beta_ind[,4]), lty=2)
legend("topright", legend=c("Agg", "Ind"), lty=1:2)

########### plot the posterior log-likelihood
matplot(out$llike[burnin:(R/keep)], type="l", xlab="Iterations", ylab=" ", main="Posterior Log-Likelihood")
mean(out$llike[burnin:(R/keep)])
## model comparison
logMargDenNR(out$llike[burnin:(R/keep)])
out$llike[1:2000]
###############plot of the rejection rate
plot(out$reject, type="l", xlab="Iterations", ylab=" ", main="Rejection Rate of the Metropolis-Hastings Algorithm")
plot(density(beta_agg[,1]), main="",xlim=c(1, 3), ylim=c(0,7))
lines(density(beta_ind[,1]), lty=2)
legend("topright", legend=c("Agg", "Ind"), lty=1:2)

### plot the erc parameters
plot(out$betadraw)
### plot the variance-covariance matrix
plot(out$Vbetadraw)


##### save the values of beta for each individual#########
m_beta=beta975=beta025=rep(0, nhh) 
matrix(rep(0,nhh*nvar), ncol=nvar)
for (i in 1:nhh) 
{
	betaifull=out$betadraw[i,1,burnin:R/keep]
  beta025[i] =  quantile(betaifull,probs =.025)
  beta975[i] =  quantile(betaifull,probs =.975)
  m_beta[i] = mean(betaifull)
}
beta_plot=data.frame(ID=1:nhh, beta025=beta025, beta975=beta975, beta_m=m_beta)

p1= ggplot(data= beta_plot,
         aes(reorder(ID, m_beta), ymin=beta025, ymax=beta975))+
  geom_linerange(colour="grey43") +
  geom_point(data = beta_plot,
             aes(reorder(ID, m_beta), y = m_beta),
             colour = "black", size = .75)+
  theme(axis.ticks.x = element_blank(), axis.text.x = element_blank())+
  labs(y = "Fairness parameters value (in log terms)",
       x = "Subjects (ordered by estimated fairness concerns)")

p1


betaest=colMeans(betai)
betaest=exp(apply(out$Deltadraw[burnin:(R/keep),],2,mean))
write.table(betai, file = "betaiERC.txt", sep = "\t", row.names = TRUE, col.names = FALSE)

hist(betai[,1], breaks=30, main="", xlab="The fairness parameter b (log)", ylab="Frequency", ylim=c(), xlim=c(0, 200))
data_fairness = betai[,1]

## country efects footnote
## Japan 2, Israel 1, Yugoslavia 3, USA 4
country=rep(0, nhh)
for (i in 1:nhh)
country[i]=ldata[[i]]$country[1]
analysis=as.data.frame(cbind(country, betai))

# One Way Anova 
fit <- aov(analysis[,2] ~ as.factor(analysis[,1]), data=analysis) 
TukeyHSD(fit)

## corr between taualpha and utility of beta
b=betai[,1]
#bA=exp(mean(oldbetas[,1]))
taualpha=betai[,2]
taubeta=betai[,3]
tau1=betai[,4]
# compute utility
offer=rep(0, nhh*nround)
for (i in 1:nhh)
  offer[((i-1)*nround+1):(nround*i)]=ldata[[i]]$offer
# utility of B if accept
# initialize the utilities
Butility=alphapar=rep(0, nhh*nround)
for (i in 1:nhh)
  {
  offer=ldata[[i]]$offer/10
  c=10
UBAcc=rep(0, nround)
UBAcc[offer<=1/2]=c*(offer[offer<=1/2]-(betai[i,1]/2)*((offer[offer<=1/2]-1/2)^2)) 
UBAcc[offer>1/2]=c*offer[offer>1/2]
Butility[((i-1)*nround+1):(nround*i)]=UBAcc
alphapar[((i-1)*nround+1):(nround*i)]=rep(betai[i,2], nround)
    }
cor(Butility, alphapar)
sillytry=rep(0,nhh)
for (i in 1:nhh)
sillytry[i]=Butility[((i-1)*nround+10)]
cor(sillytry, betai[,2])
############### plot of the erc coefficients over the entire # of draws
par(mfrow=c(2,2))
matplot(out$Deltadraw[,nz*0+1], type="l", xlab="Iterations", ylab=" ", main="Fairness parameter b")
matplot(out$Deltadraw[,nz*1+1], type="l", xlab="Iterations", ylab=" ", main="A player's base decision parameter τα")
matplot(out$Deltadraw[,nz*2+1], type="l", xlab="Iterations", ylab=" ", main="B player's base decision parameter τβ")
matplot(out$Deltadraw[,nz*3+1], type="l", xlab="Iterations", ylab=" ", main="Experience parameter τ1")

########## plot of the diagonal elements of the covarience matrix
index=nz*c(0:3)+1 
matplot(out$Vbetadraw[,index], type="l", xlab="Iterations/10", ylab=" ", main="VbetaDraws")

########### plot the posterior log-likelihood
mean(out$llike[burnin:(R/keep)])
matplot(out$llike[burnin:(R/keep)], type="l", xlab="Iterations", ylab=" ", main="Posterior Log-Likelihood")

## model comparison
logBF=logMargDenNR(out$llike[burnin:(R/keep)])-logMargDenNR(out$llike[burnin:(R/keep)])

###############plot of the rejection rate
plot(out$reject, type="l", xlab="Iterations", ylab=" ", main="Rejection Rate of the Metropolis-Hastings Algorithm")

#### save the posterir distribution of the erc parameters
postdistr=cbind(t(matrix(apply(exp(out_gamma$Deltadraw[burnin:(R/keep),]),2,mean),ncol=nvar)), 
                t(matrix(apply(exp(out_gamma$Deltadraw[burnin:(R/keep),]),2,
                               function(x) quantile(x,probs=c(.025, .975))),ncol=nvar)))
write.table(postdistr, file = "PostDistrNewModel.txt", sep = "\t", row.names = TRUE, col.names = FALSE)

## save the posterior varcov
postvcov=t(matrix(apply(out$Vbetadraw[burnin:(R/keep),],2,mean),ncol=nvar))
postvcovsd=t(matrix(apply(out$Vbetadraw[burnin:(R/keep),],2, function(x) quantile(x,probs=c(.025, .975))),ncol=nvar))
write.table(postvcov, file = "Postvcov.txt", sep = "\t", row.names = TRUE, col.names = FALSE)

############################################################
# Compute rejection rates per offer and per round
##############################################################

### compute the probability of acceptance 
PbBall=array(double(10 * 11 * nhh), dim = c(nhh,10, 11))
 
for (i in 1:nhh) 
{
Sigma=c(0, .1, .2, .3, .4, .5, .6, .7, .8, .9, 1)
UBAcc=rep(1, 11)
c=10	
for (k in 1:length(Sigma))
{
#utility of B if B accepts
### this is computed using each individual's fairness parameter for the B player 
if (Sigma[k]<=.5) UBAcc[k]=c*(Sigma[k]-((betai[i,1]/2)*(Sigma[k]-1/2)^2)) 
	else  UBAcc[k]=c*Sigma[k]  }
	
# utility of A if B rejects
UBRej=rep(0, 11)

#initialize probability matrix
PbB=matrix(rep(0, 11*10), ncol=11)

for (n in 1:length(ldata[[1]]$Round))
{
#### probability of B to accept a specific offer
### this is computed with each B player's coeficient of certitude and their experience parameter
PbB[n,]=
exp((betai[i,3]*(1+betai[i,4]*(ldata[[1]]$Round[n]-1)))*UBAcc)/(1+exp(betai[i,3]*(1+betai[i,4]*(ldata[[1]]$Round[n]-1))*UBAcc))

}
### i store all of them in a big array
PbBall[i, ,]=PbB
}

###############Overall average predicted acceptance rates
AvPbBall=colMeans(PbBall)

##compute the predicted average offer per round
AvOffer= matrix(rep(0,nhh*10), ncol=nhh)
ModelPbOffer= matrix(rep(0,nhh*11), ncol=nhh)
ModelPbReject= matrix(rep(0,nhh*11), ncol=nhh)
PbRejectRound=matrix(rep(0,nhh*10),ncol=nhh)
PbAall=array(double(10 * 11 * nhh), dim = c(nhh,10, 11))

for (i in 1:nhh) 
{
Sigma=c(0, .1, .2, .3, .4, .5, .6, .7, .8, .9, 1)
UAAcc=rep(1, 11)
c=10	
#utility of A if B accepts
## this is computed with the average of the fairness parameter over all B players. 
### essentailly all A players have the same utility if B payers accept an offer. 
### we agreed to do this as we can't estimate A players' fairness parameters
for (k in 1:length(Sigma))
{if (Sigma[k]>.5) UAAcc[k]=c*((1-Sigma[k])-((betai[i,1]/2)*((1-Sigma[k])-1/2)^2)) 
	else  UAAcc[k]=c*(1-Sigma[k])   }
# utility of A if B rejects
UARej=UBRej
#initialize probability matrices
ExUAAcc=matrix(rep(0, 11*10), ncol=11)
PbA=matrix(rep(0, 11*10), ncol=11)
PbRejectperRound=rep(0,10)
for (n in 1:length(ldata[[1]]$Round))
{

#A's expected utility if A offers X to B
ExUAAcc[n,]=UAAcc*PbBall[i,n,] #+UARej*(1-PbB)
#Pb of A to offer X
### computed with individual values for the coeficients of certitude and the experience effects for every A player
PbA[n,]=(exp((betai[i,2]*(1+betai[i,4]*(ldata[[1]]$Round[n]-1)))*ExUAAcc[n,]))/sum(exp(betai[i,2]*(1+betai[i,4]*(ldata[[1]]$Round[n]-1))*ExUAAcc[n,]))

}

### probability of A to offer sigma times the offer for each A player
### multiply each probability of offer by the offer (c*sigma) 
### add them together tpo get the average offer per round
Average_offer=colSums(t(PbA)*c*Sigma)	
#### average probability of an offer of sigma for each A player over all rounds of the game
ModelPb_Offer=colMeans(PbA)
################################
###############################
# this is the probability of reject given sigma
### computed for each B player with their own fairness, tau and experience effects
### it's the average probability of reject over all rounds for each offer for each player B
Pb_reject=1-(colMeans(PbBall[i,,]))
# probability of reject per round
## PbBall*PbA is the probability of accepting an offer of sigma* proabbility of 
#### A player of making such an offer (both individual specific)
#### rowSums means that I sum it over all values of sigma
### 1-rowSums() transfer into probability of reject
PbRejectperRound=1-rowSums(PbBall[i,,]*PbA)

### store the computed values for each individual in arrays
ModelPbOffer[,i]=ModelPb_Offer
ModelPbReject[,i]=Pb_reject
PbRejectRound[,i]=PbRejectperRound
AvOffer[,i]=Average_offer
PbAall[i, , ]=PbA
}

###############Overall average predicted offers 
PredictedOffer=c(AvOffer)
### i take the grand mean of the average offers over all respondents over all rounds
mean(PredictedOffer, na.rm=T)
### grand mean over all offers made during the game
mean(floor(DatasetRothFull$Offer))

################################################################
#Figure 1 ERC 
##################################################################

#Figure 1A
### average over all respondents per sigma
AvModelPbOffer=rowMeans(ModelPbOffer,na.rm=T)

#### Observed probability of offer per c*sigma
## initialize the matrix of observed probability of offer per all individuals per all rounds

ObsPbOffer=matrix(rep(0, 11*nhh),ncol=nhh)
### for each individual
for (i in 1:nhh)
{
	## count observed offer
	ObsPb_Offer=rep(0, 11)
	for (j in 1:length(ObsPb_Offer))
		{
		## compute the probability of an offer 
		#### the sum variabe counts how many observed offers of 0 to 10 are there in the offer vector 
		#### for the 10 rounds
		### that is divided by 10 rounds
			ObsPb_Offer[j]=sum(ldata[[i]]$offer==j-1)/10
		}
		### this matrix has probabilities of a specific offer as row and individuals as column vectors
		ObsPbOffer[,i]=ObsPb_Offer
}

## this is the grant mean of the observed probability of a specific offer
### it's a vector or offers and their probabilities over all respondents
AvObsPbOffer=rowMeans(ObsPbOffer)

# plot the average observed probability of offer vs. average model probability of offer. Figure 1A
par(mfrow=c(1,2))
####### model probability of offer
plot(Sigma,AvModelPbOffer, type="o", ylim=c(0,1), xlim=c(0, 1), ylab="Average Probability of Offer",
	 xlab="Offer")
lines(Sigma, AvObsPbOffer, type= "o", pch=22, lty=2)
legend(x=.6, y=0.9, c("Observations", "Model"), pch=22:21, lty=2:1)

#Figure 1B

#### average over all respondents for the probability of reject
### 
AvModelPbReject=rowMeans(ModelPbReject)

####################################################################
## Weighting

## 0,1 big array for the offers (stacks choice matrices together)
PbOfferperRound=array(double(10 * 11 * nhh), dim = c(nhh,10, 11))

for (i in 1:nhh) 
{
  PbOfferperRound[i, , ]=ldata[[i]]$Choice
}
PbOffersmall=colMeans(PbOfferperRound)
ModelAcceptedOffers=colMeans(PbBall)
ModelOffers=colMeans(PbAall)

## sum of predicted acceptance rate with the OBSERVED pb of offer
WeigthtedOBSPbAccept=colSums(PbOffersmall*ModelAcceptedOffers)/colSums(PbOffersmall)
WeigthtedOBSPbReject=1-WeigthtedOBSPbAccept

## sum of predicted acceptance rate with the MODEL (predicted) pb of offer
WeigthtedModelPbAccept=colSums(ModelOffers*ModelAcceptedOffers)/colSums(ModelOffers)
WeigthtedModelPbReject=1-WeigthtedModelPbAccept

## rejection rates only for offers made
try= array(double(10 * 11), dim = c(10, 11))
for (j in 1:nround)
  {for (k in 1:noffer)
    {try[j,k]=sum(PbBall[,j,k][PbOfferperRound[,j,k]==1])/sum(PbOfferperRound[,j,k][PbOfferperRound[,j,k]==1])
    }
  }
new=1-colMeans(try, na.rm=T)

###############################################################

mean(AvModelPbReject)
### observed probability of rejection
### observed number of rejected offers per respodent
ObsReject=matrix(rep(0, 11*nhh), ncol=nhh)
### observed number of offers per respodent
ObsOffer=matrix(rep(0, 11*nhh), ncol=nhh)
for (i in 1:nhh)
{
	### for each repondnets, initialize a vector of rejected offers
	ObsReject_Offer=rep(0, 11)
	### for each repondnets, initialize a vector to count specific offers
	Obs_Offer=rep(0, 11)
	### take the response of every individual
	a=ldata[[i]]$Response
	### subset the nuber of rejections
	b=which(a==0)
	for (j in 1:length(ObsReject_Offer))
		{
			### count for each offer the sumber of rejected offers
			ObsReject_Offer[j]=sum(ldata[[i]]$offer[b[1:length(b)]]==j-1)
			### count how many times a specific offer was made
			Obs_Offer[j]=sum(ldata[[i]]$offer==j-1)
	}	
		## store for each B player the number of rejected offers
		ObsReject[,i]=ObsReject_Offer
		## store for each B palyer the number of offers he received
		ObsOffer[,i]=Obs_Offer
}

# the number of offers rejected for each sigma
## sum of all rejections for each offer, ra.rm=T is to make sure i don't have errors
ObsRejectOffer=rowSums(ObsReject, na.rm=TRUE)

## the number of offers for each sigma
#### sum of all offers for each sigma, agin making sure i don't get errors
ObsOfferOverall=rowSums(ObsOffer, na.rm=TRUE)

## observed probability of reject
### divide the observed number of rejections per offer
### to the number of effers for each sigma
AvObsPbReject=ObsRejectOffer/ObsOfferOverall
mean(AvObsPbReject)

## plot model vs. obs probability of reject. figure 1B
plot(Sigma,AvModelPbReject, type="o", ylim=c(0,1), xlim=c(0, 1), ylab="Average Probability of Reject", xlab="Offer", main="weights with MODEL (PREDICTED) pb of offer")
lines(Sigma, AvObsPbReject, type= "o", pch=22, lty=2)
legend(x=.6, y=.9, c("Observations", "Model"), pch=22:21, lty=2:1)

plot(Sigma,new, type="o", ylim=c(0,1), xlim=c(0, 1), ylab="Average Probability of Reject", xlab="Offer", main="Average for observed offers")
lines(Sigma,AvObsPbReject , type= "o", pch=22, lty=2)
legend(x=.6, y=.9, c("Observations", "Model"), pch=22:21, lty=2:1)

#### corr btw average observed probability of offer and average predicted probability of offer
cor(AvObsPbOffer, AvModelPbOffer, use="complete.obs")
#### corr btw average observed probability of reject and average predicted probability of reject
cor(AvObsPbReject,AvModelPbReject, use="complete.obs")


###################################################################
# Figure 2 ERC 2.1
###################################################################

AvModelRejectRound=rowMeans(PbRejectRound, na.rm=T)

###############Obs rejection rate per round
ObsRejectRate=matrix(rep(0, 10*nhh), ncol=nhh)
for (i in 1:nhh)
{
	ObsReject=rep(0, 10)
	for (j in 1:length(ldata[[i]]$Response))
		{
			ObsReject[j]=sum(ldata[[i]]$Response[j]==0)
		}
		ObsRejectRate[,i]=ObsReject
}

AvObsRejectRate=rowSums(ObsRejectRate)/nhh
mean(AvObsRejectRate)

plot(ldata[[1]]$Round,AvModelRejectRound, type="o", ylim=c(0,.5), xlim=c(1, 10), ylab="Average Probability of Reject", xlab="Round", xaxt="n")
lines(ldata[[1]]$Round, AvObsRejectRate, type= "o", pch=22, lty=2)
axis(1, at=1:10,labels=1:10)
legend(x=7, y=.45, c("Observations", "Model"), pch=22:21, lty=2:1)


###################################################################
# Figure 3 ERC 2.1
###################################################################

#model probability of offer per round
AvPbAall=colMeans(PbAall, na.rm=T)

### observed probability of offer for rounds 9 and 10
### essentially is the same thing as in the figure 1B, just for the 9th and 10th replies. 
ObsPbOffer910=matrix(rep(0, 11*nhh), ncol=nhh)
### for each individual
for (i in 1:nhh)
{
	ObsPb_Offer910=rep(0, 11)
	for (j in 1:length(ObsPb_Offer))
		{
		## compute the probability of an offer 
		#### the sum variabe counts how many observed offers of 0 to 10 are there in the offer vector 
		#### for the last 2 rounds
		### that is divided by 2 rounds
			ObsPb_Offer910[j]=sum(ldata[[i]]$offer[9:10]==j-1)/2
		}
		ObsPbOffer910[,i]=ObsPb_Offer910
}

### mean probability of offer for all individuals for the last 2 rounds 
AvObsPbOffer910=rowMeans(ObsPbOffer910)

### observed probability of offer for rounds 1 and 2
ObsPbOffer12=matrix(rep(0, 11*nhh), ncol=nhh)
for (i in 1:nhh)
{
	ObsPb_Offer12=rep(0, 11)
	for (j in 1:length(ObsPb_Offer))
		{
		## compute the probability of an offer 
		#### the sum variabe counts how many observed offers of 0 to 10 are there in the offer vector 
		#### for the first 2 rounds
		### that is divided by 2 rounds
			ObsPb_Offer12[j]=sum(ldata[[i]]$offer[1:2]==j-1)/2
		}
		## store results for each individual
		ObsPbOffer12[,i]=ObsPb_Offer12
}

### mean probability of offer for all individuals for the first 2 rounds 
AvObsPbOffer12=rowMeans(ObsPbOffer12)
### observed probability of rejection

## plot model vs. obs probability of offer for the 1st vs. the last rounds

par(mfrow=c(1,2))

####### model probability of offer , rounds 1 vs. 10
plot(Sigma,AvPbAall[1,], type="o", ylim=c(0,.8), xlim=c(0, 1), ylab="Average Probability of Offer",
	 xlab="Offer")
lines(Sigma, AvPbAall[10,], type= "o", pch=22, lty=2)
legend(x=.61, y=.8, c("Round 1", "Round 10"), pch=22:21, lty=2:1)
####### observed probability of offer, rounds 1-2 vs. 9-10
plot(Sigma, AvObsPbOffer12, type="o", ylim=c(0,.8), xlim=c(0, 1), ylab="Average Probability of Offer", xlab="Offer")
lines(Sigma, AvObsPbOffer910, type= "o", pch=22, lty=2)
legend(x=.55, y=.8, c("Rounds 1-2", "Rounds 9-10"), pch=22:21, lty=2:1)

########################### 
##### "out-of-sample" hit rate
###########################

hitRate=rep(0, nhh)
modelFit=rep(0,nhh)
modelFit2=rep(0,nhh)

for(i in 1:nhh)
{ 	 
	
 		b=betai[i,1]
		taualpha=betai[i,2]
		taubeta=betai[i,3]
		tau1=betai[i,4]
		
Sigma=c(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
# c(entire pay)*sigma(share of the pay A offers)
c=10
# utility of B if accept
UBAcc=UAAcc=rep(1, 11)
for (k in 1:length(Sigma))
{
	
if (Sigma[k]<=5) 	UBAcc[k]=c*((Sigma[k]/c)-(b1/2)*(((Sigma[k]/c)-0.5)^2))
	else  UBAcc[k]=Sigma[k] }
#utility of B if reject
UBRej=rep(0, 11)

#utility of A if B accepts
for (k in 1:length(Sigma))
{if (X[k]>=5) UAAcc[k]=c*((1-Sigma[k]/10)-((b2/2)*((1-Sigma[k]/10)-1/2)^2)) 
	else  UAAcc[k]=10-Sigma[k] }

# utility of A if B rejects
UARej=UBRej
#initialize probability matrices
PbB=matrix(rep(0, 11*10), ncol=11)
ExUAAcc=matrix(rep(0, 11*10), ncol=11)
PbA=matrix(rep(0, 11*10), ncol=11)

for (n in 9:10)
{
PbB[n,]=
exp((taubeta*(1+tau1*ldata[[1]]$Round[n]))*UBAcc)/(exp((taubeta*(1+tau1*ldata[[1]]$Round[n]))*UBRej)+exp(taubeta*(1+tau1*ldata[[1]]$Round[n])*UBAcc))
#A's expected utility if A offers X to B
ExUAAcc[n,]=UAAcc*PbB[n,] #+UARej*(1-PbB)
#Pb of A to offer X
PbA[n,]=(exp((taualpha*(1+tau1*ldata[[1]]$Round[n]))*ExUAAcc[n,]))/sum(exp((taualpha*(1+tau1*ldata[[1]]$Round[n]))*ExUAAcc[n,]))
 
}

ldata[[i]]$Pb=PbA*PbB

predCh=rep(0, 10)
ind=rep(0, 10)

 for (k in 9:10)
	{ 
for (j in 1:ncol(ldata[[1]]$Pb))
 {if (ldata[[i]]$Pb[k, j]==max(ldata[[i]]$Pb[k, ])) predCh[k]=j-1}


	if (predCh[k]==ldata[[i]]$offer[k]) ind[k]=1	
}

 hitRate[i]=sum(ind[9:10])/2
 if(hitRate[i]>0.5)  modelFit[i]=1
 	if(hitRate[i]>0)  modelFit2[i]=1
	GoF=sum(modelFit)/nhh
	Gof2=sum(modelFit2)/nhh
    
}
 
## the overall out-of-sample hit rate 
OverallOutOfSampleHR=sum(hitRate)/nhh

IndOutOfSamplePbOffer=ldata[[1]]$Pb
for (i in 2:nhh)
{
	IndOutOfSamplePbOffer=rbind(IndOutOfSamplePbOffer, ldata[[i]]$Pb)
	}

### observed probability of offer for rows 9 to 10
ObsPbOffer9=matrix(rep(0, 11*nhh), ncol=nhh)
ObsPbOffer10=matrix(rep(0, 11*nhh), ncol=nhh)
for (i in 1:nhh)
{
	ObsPb_Offer9=rep(0, 11)
	ObsPb_Offer10=rep(0, 11)
	for (j in 1:length(ObsPb_Offer9))
		{
			ObsPb_Offer9[j]=sum(ldata[[i]]$offer[9]==j-1)
			ObsPb_Offer10[j]=sum(ldata[[i]]$offer[10]==j-1)
		}
		ObsPbOffer9[,i]=ObsPb_Offer9
		ObsPbOffer10[,i]=ObsPb_Offer10
}

AvObsPbOffer9=rowMeans(ObsPbOffer9)
AvObsPbOffer10=rowMeans(ObsPbOffer10)


###################################################################
# Figure 4 ERC 2.1
###################################################################

########## "out-of-sample" fit plots

par(mfrow=c(1,2))

####### model probability of offer
plot(Sigma,AvObsPbOffer9, type="o", col="blue", ylim=c(0,.7), xlim=c(0, 10), ylab="Average Probability of Offer",
	 xlab="Offer for Round 9")
lines(Sigma, IndOutOfSamplePbOffer[9,], col="red", type= "o", pch=22, lty=2)
legend(x=5, y=.7, c("Model", "Observations"), col=c("red", "blue"), pch=22:21, lty=2:1)

plot(Sigma,AvObsPbOffer10, type="o", col="blue", ylim=c(0,.7), xlim=c(0, 10), ylab="Average Probability of Offer", 
xlab="Offer for Round 10")
lines(Sigma, IndOutOfSamplePbOffer[10,], col="red", type= "o", pch=22, lty=2)
legend(x=5, y=.7, c("Model", "Observations"), col=c("red", "blue"), pch=22:21, lty=2:1)

### fixed effects
beta=matrix(rep(c(6, 1.2, .8,.35), 11), ncol=4, byrow=T)
beta[,1]=c(0, 2, 4, 6, 8, 10, 30,50, 70, 120, 150)
X=ldata[[83]]$Response
y=ldata[[83]]$Choice
ll=rep(0, nrow(beta))
for (i in 1:nrow(beta))
ll[i]=erc.lk(beta[i,], X, y)
plot(ll, type="l", xaxt='n',  main="Likelihood function", xlab="Fairness parameter values")
axis(1,at=1:11, labels=c("0","2","4", "6", "8", "10", "30", "50", "70", "100", "150" ))


## simulation of beta players choices at 40%
erc.sim<- function (beta,y)
	{ 			
		b=beta[1]
		taualpha=beta[2]
		taubeta=beta[3]
		tau1=beta[4]
		
# c(entire pay)*sigma(share of the pay A offers)
Sigma=c(0, .1, .2, .3, .4, .5, .6, .7, .8, .9, 1)
c=10

# utility of B if accept
# initialize the utilities
UBAcc=UAAcc=rep(0, 11)
for (k in 1:length(Sigma))
{if (Sigma[k]<=.5) UBAcc[k]=c*(Sigma[k]-(b/2)*((Sigma[k]-1/2)^2)) 
	else  UBAcc[k]=c*Sigma[k] }

#utility of B if reject
UBRej=rep(0, 11)

#initialize probability matrices
PbB=matrix(rep(0, 11*10), ncol=11)

# compute probability matrices for the probability of B to accept, expected value of A in case B accepts and the probability of A to make an offer of sigma
for (n in 1:length(ldata[[1]]$Round))
{
PbB[n,]=(exp((taubeta*(1+tau1*(ldata[[1]]$Round[n]-1)))*UBAcc))/(1+exp(taubeta*(1+tau1*(ldata[[1]]$Round[n]-1))*UBAcc))

}

## simultated X
unif=runif(nrow(y),0,1)
X=ifelse(unif<PbB[,5],1,0)
Xbinom=rbinom(10, 1, PbB[,5])

return(list(X=X, Xbinom=Xbinom))
}

coef=matrix(rep(c(6, 1.8, .8,.95), 100), ncol=4, byrow=T)
coef[,1]=seq(0, 99, 1)
y=matrix(rep(0, 11*10), ncol=11)
y[,5]=1
Xsim=matrix(rep(0, 10*nrow(coef)), ncol=10)
Xbinom=matrix(rep(0, 10*nrow(coef)), ncol=10)
ll=rep(0, nrow(coef))
for (i in 1:nrow(coef))
	{sim=erc.sim(coef[i,], y)
	Xsim[i,]=sim$X
	Xbinom[i,]=sim$Xbinom
	ll[i]=erc.lk(coef[i,],Xbinom[i,], y)
}
plot(ll)

### ERC presentation 

  b=6
  taualpha=1.2
  taubeta=0.8
  tau1= 0.1
  noffer=11
  # c(entire pay)*sigma(share of the pay A offers)
  Sigma=c(0, .1, .2, .3, .4, .5, .6, .7, .8, .9, 1)
  c=10
  
  # utility of B if accept
  # initialize the utilities
  UBAcc=UAAcc=rep(0, noffer)
  UBAcc[Sigma<=.5]=c*(Sigma[Sigma<=.5]-(b/2)*((Sigma[Sigma<=.5]-1/2)^2)) 
  UBAcc[Sigma>.5]=c*Sigma[Sigma>.5]
 
  #utility of B if reject
  UBRej=UAAcc=rep(0, noffer)
  #utility of A if B accepts
  UAAcc[Sigma>=.5]=c*((1-Sigma[Sigma>=.5])-(b/2)*(((1-Sigma[Sigma>=.5])-1/2)^2)) 
  UAAcc[Sigma<.5]=c*(1-Sigma[Sigma<.5])

b=0
UBAcc0=UAAcc0=rep(0, noffer)
UBAcc0[Sigma<=.5]=c*(Sigma[Sigma<=.5]-(b/2)*((Sigma[Sigma<=.5]-1/2)^2)) 
UBAcc0[Sigma>.5]=c*Sigma[Sigma>.5]
#utility of A if B accepts
UAAcc0[Sigma>=.5]=c*((1-Sigma[Sigma>=.5])-(b/2)*(((1-Sigma[Sigma>=.5])-1/2)^2)) 
UAAcc0[Sigma<.5]=c*(1-Sigma[Sigma<.5])

  #initialize probability matrices
  PbB=matrix(rep(0, noffer*nround), ncol=noffer)
  ExUAAcc=matrix(rep(0, noffer*nround), ncol=noffer)
  PbA=matrix(rep(0, noffer*nround), ncol=noffer)
  
  # compute probability matrices for the probability of B to accept, expected value of A in case B accepts and the probability of A to make an offer of sigma  
  PbB=(exp((taubeta*(1+tau1*(ldata[[1]]$Round-1)))%*%t(UBAcc)))/(1+exp((taubeta*(1+tau1*(ldata[[1]]$Round-1)))%*%t(UBAcc)))
  #A's expected utility if A offers X to B
  ExUAAcc=t(UAAcc*t(PbB))
  #Pb of A to offer X
  PbA=((exp((taualpha*(1+tau1*(ldata[[1]]$Round-1)))*ExUAAcc))/rowSums(exp((taualpha*(1+tau1*(ldata[[1]]$Round-1)))*ExUAAcc)))
  
  ## probability of either reject or accept, computed by taking into consideration the response of player B
  PbBR= matrix(rep(0, noffer*nround), ncol=noffer)
  for (l in 1:ncol(y))
  { for (m in 1:nrow(y))
  {
    if (X[m]==0 && y[m,l]==1) PbBR[m,l]=1-PbB[m,l]
    else PbBR[m,l]=PbB[m,l]
  } 	
  }
  
  logl=sum(log(rowSums(PbA*PbBR*y)))
label=c*Sigma
### plot of feedback score
par(mfrow=c(1,2))
plot(UBAcc,type="l",col="blue", ylab="B player's utility of acceppting an offer", xlab="Offer", xaxt="n")
lines(UBAcc0, type="l", col="red", lty=2)
axis(1, at=1:11, labels=label,las=1)
legend("bottomright", col=c("blue", "red"), lty=1:2, legend=c("Average fairness", "No fairness"))
## A plyers
plot(UAAcc, type="l",col="blue", ylab="A player's utility if accept", xlab="Offer", xaxt="n" )
lines(UAAcc0, type="l", col="red", lty=2)
axis(1, at=1:11, labels=label,las=1)
legend("bottomleft", col=c("blue", "red"), lty=1:2, legend=c("Average fairness", "No fairness"))

## likleihood of accepting offers of 1 for the individual heterogeneity model. 
setwd("/Users/alina/Documents/hb erc results v4")
load("erc mix 2 big.RData")
load("hberc results v4 indhet.RData")
R=50000
burnin=40000
keep=1
nhh=116
nvar=4
betai=matrix(rep(0,nhh*nvar), ncol=nvar)

for (i in 1:nhh) 
{
	
meanbeta=rowSums(outercDP$betadraw[i,,burnin:R/keep])/((R/keep)-burnin)
betai[i,]=meanbeta

}
hist(betai[,1])
b=betai[,1] 
length(b[b>4])/1160
quantile(b, prob=c(0.025, 0.975))
## only for QRE model
##betai=cbind(rep(0, nhh), betai)

### compute the probability of acceptance 
PbBall=array(double(10 * 11 * nhh), dim = c(nhh,10, 11))
 
for (i in 1:nhh) 
{
Sigma=c(0, .1, .2, .3, .4, .5, .6, .7, .8, .9, 1)
UBAcc=rep(1, 11)
c=10	
for (k in 1:length(Sigma))
{
#utility of B if B accepts
### this is computed using each individual's fairness parameter for the B player 
if (Sigma[k]<=.5) UBAcc[k]=c*(Sigma[k]-((betai[i,1]/2)*(Sigma[k]-1/2)^2)) 
	else  UBAcc[k]=c*Sigma[k]  }
	
# utility of A if B rejects
UBRej=rep(0, 11)

#initialize probability matrix
PbB=matrix(rep(0, 11*10), ncol=11)

for (n in 1:length(ldata[[1]]$Round))
{
#### probability of B to accept a specific offer
### this is computed with each B player's coeficient of certitude and their experience parameter
PbB[n,]=
exp((betai[i,3]*(1+betai[i,4]*(ldata[[1]]$Round[n]-1)))*UBAcc)/(1+exp(betai[i,3]*(1+betai[i,4]*(ldata[[1]]$Round[n]-1))*UBAcc))

}
### i store all of them in a big array
PbBall[i, ,]=PbB
}

###############Overall average predicted acceptance rates
AvPbBall=colMeans(PbBall)
## number of people accepting offers lower than 2 with 60% pb  
length(PbBall[,10,5][PbBall[,10,5]<0.25])
try=rep(0,nhh)
### check if they're different people
for (i in 1:nhh)
  {if(PbBall[i,10,5]<0.25) try[i]=100 }

freq3c=rep(0,11)
for (i in 0:10)
freq3c[i]=length(PbBall[,,4][PbBall[,,5]>i/10])

## number of people rejecting offers of 4 and above with 60% pb =45
Pbreject=1-PbBall
freq4c=rep(0,11)
for (i in 0:10)
freq4c[i]=length(Pbreject[,,2][Pbreject[,,2]>i/10])

## noncum distr
freq3cn=rep((1033-1160), 10)
for (i in 2:10)
freq3cn[i]=freq3c[i]-freq3c[i-1]

## DP vs. SN - ind b>0
R=50000
burnin=40000
try=t(matrix(apply(outercDPbig$betadraw[,1,burnin:(R/keep)],1,
               function(x) quantile(x,probs=c(.025, .975))),ncol=116))

length(try[try[,2]<2.2])

