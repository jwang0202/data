censReg.adj <- function( formula, left = 0, right = Inf,
                     data = sys.frame( sys.parent() ), subset = NULL, start = NULL,
                     nGHQ = 8, logLikOnly = FALSE,const = NULL,wt = NULL, ... ) {

  ##################################################
  cen = function(x,left=-Inf,right=Inf){
    x[x>=right] = right
    x[x<=left] = left
    return(x)
  }
  ## log likelihood function for cross-sectional data
  censRegLogLikCross_wt <- function( beta, yVec, xMat, left, right, 
                                  obsBelow, obsBetween, obsAbove, wt = NULL ) {
    if(is.null(wt)) wt = rep(1/length( yVec ),length( yVec ))
    wt = wt/sum(wt)
    yHat <- xMat %*% beta[ - length( beta ) ]
    sigma <- exp( beta[ length( beta ) ] )
    ll <- rep( NA, length( yVec ) )
    ll[ obsBelow ] <-
      pnorm( ( left - yHat[ obsBelow ] ) / sigma, log.p = TRUE )*wt[ obsBelow ]
    ll[ obsBetween ] <-
      (dnorm( ( yVec - yHat )[ obsBetween ] / sigma, log = TRUE ) -
      log( sigma ))*wt[ obsBetween ]
    ll[ obsAbove ] <-
      pnorm( ( yHat[ obsAbove ] - right ) / sigma, log.p = TRUE )*wt[ obsAbove ]
    
    ## gradients of log likelihood function for cross-sectional data
    grad <- matrix( NA, nrow = length( yVec ), ncol = length( beta ) )
    grad[ obsBelow, ] <-
      exp( dnorm( ( left - yHat[ obsBelow ] ) / sigma, log = TRUE ) -
             pnorm( ( left - yHat[ obsBelow ] ) / sigma, log.p = TRUE ) ) *
      cbind( - xMat[ obsBelow, , drop = FALSE ] / sigma,
             - ( left - yHat[ obsBelow ] ) / sigma )
    grad[ obsBetween, ] <-
      cbind( ( ( yVec - yHat )[ obsBetween ] / sigma ) *
               xMat[ obsBetween, , drop = FALSE ] / sigma,
             ( ( yVec - yHat )[ obsBetween ] / sigma )^2 - 1 )
    grad[ obsAbove, ] <-
      exp( dnorm( ( yHat[ obsAbove ] - right ) / sigma, log = TRUE ) -
             pnorm( ( yHat[ obsAbove ] - right ) / sigma, log.p = TRUE ) ) *
      cbind( xMat[ obsAbove, , drop = FALSE ] / sigma,
             - ( yHat[ obsAbove ] - right ) / sigma )
    grad = sweep(grad, MARGIN=1, wt, `*`)
    attr( ll, "gradient" ) <- grad
    return( ll )
  }
  
  ##################################################
  ## checking formula
  if( class( formula ) != "formula" ) {
    stop( "argument 'formula' must be a formula" )
  } else if( length( formula ) != 3 ) {
    stop( "argument 'formula' must be a 2-sided formula" )
  }
  
  ## checking limits
  # left
  if( !is.numeric( left ) ) {
    stop( "argument 'left' must be a number" )
  } else if( length( left ) != 1 ) {
    stop( "argument 'left' must be a scalar (single number)" )
  }
  # right
  if( !is.numeric( right ) ) {
    stop( "argument 'right' must be a number" )
  } else if( length( right ) != 1 ) {
    stop( "argument 'right' must be a scalar (single number)" )
  }
  # both
  if( left >= right ) {
    stop( "argument 'right' must be a larger number than argument 'left'" )
  }
  
  ## checking argument 'logLikOnly'
  if( length( logLikOnly ) != 1 ) {
    stop( "argument 'logLikOnly' must be a single logical value" )
  } else if( !is.logical( logLikOnly ) ) {
    stop( "argument 'logLikOnly' must be logical" )
  }
  if( logLikOnly && is.null( start ) ) {
    stop( "if argument 'logLikOnly' is 'TRUE',",
          " parameters must be specified by argument 'start'" )
  }
  
  ## preparing model matrix and model response
  mc <- match.call( expand.dots = FALSE )
  m <- match( c( "data", "subset" ), names( mc ), 0 )
  mf <- mc[ c( 1, m ) ]
  mf$formula <- formula
  attributes( mf$formula ) <- NULL
  mf$na.action <- na.pass
  mf[[ 1 ]] <- as.name( "model.frame" )
  mf <- eval( mf, parent.frame() )
  # remove unused levels
  for( i in 1:ncol( mf ) ) {
    if( is.factor( mf[[ i ]] ) ) {
      mf[[ i ]] <- factor( mf[[ i ]] )
    }
  }
  mt <- attr( mf, "terms" )
  xMat <- model.matrix( mt, mf )
  xNames <- colnames( xMat )
  yVec <- model.response( mf )
  yName <- as.character( formula )[ 2 ]
  if( length( yVec ) != nrow( xMat ) ) {
    stop( "the number of observations of the endogenous variable (",
          length( yVec ), ") is not equal to the number of observations",
          " of the exogenous variables (", nrow( xMat ), ")" )
  }
  
  ## extract information on panel structure of data set
  isPanel <- inherits( data, c( "pdata.frame", "plm.dim" ) )
  if( isPanel ) {
    if( inherits( data, "pdata.frame" ) ) {
      # current panel data format from pkg plm
      pIndex <- index( data )
    } else if( inherits( data, "plm.dim" ) ) {
      # deprecated panel data format from pkg plm
      pIndex <- data[ , 1:2 ]
    } else {
      stop( "internal error: please contact the maintainer",
            " of the 'censReg' package" )
    }
    ## check if observations are ordered with respect to names of individuals
    # (theoretically, it is not required that the observations are ordered
    # alphabetically with respect to individuals' names but
    # if the individuals are not in the same order for each time period,
    # the observations are allocated to a wrong individual)
    if( !identical( order( pIndex[[ 1 ]] ), 1:length( pIndex[[ 1 ]] ) ) ) {
      stop( "names of individuals in attributes(data)$index[[1]]",
            " must be in alphabetical order but they are not;",
            " please fix this and re-run censReg()." )
    }
    
  }
  
  ## check if endogenous variable is within limits
  if( any( yVec[ !is.na( yVec ) ] < left ) ) {
    warning( "at least one value of the endogenous variable is smaller than",
             " the left limit" )
  } else if( any( yVec[ !is.na( yVec ) ] > right ) ) {
    warning( "at least one value of the endogenous variable is larger than",
             " the right limit" )
  }
  
  ## detect and remove observations with NAs, NaNs, and INFs
  validObs <- rowSums( is.na( cbind( yVec, xMat ) ) |
                         is.infinite( cbind( yVec, xMat ) ) ) == 0
  yVec <- yVec[ validObs ]
  xMat <- xMat[ validObs, , drop = FALSE ]
  if( isPanel ) {
    pIndex <- pIndex[ validObs, , drop = FALSE ]
    indNames <- unique( pIndex[[ 1 ]] )  # 'names' of individuals
    nInd <- length( indNames )           # number of individuals
    timeNames <- unique( pIndex[[ 2 ]] ) # 'names' of time periods
    nTime <- length( timeNames )         # number of time periods
  }
  
  ## starting values
  nParam <- ncol( xMat ) + 1
  if( isPanel ) {
    nParam <- nParam + 1
  }
  if( is.null( start ) ) {
    if( isPanel ) {
      assign( "validObs2", validObs, inherits = TRUE )
      if( length( attr( terms( formula ), "term.labels" ) ) > 0 ) {
        # Random effects panel model estimation for starting values
        rEff <- plm( formula, data = data, subset = validObs2,
                     effect = "individual", model = "random" )
        start <- c( coef( rEff ),
                    0.5 * log( rEff$ercomp$sigma2[[ "id" ]] ),
                    0.5 * log( rEff$ercomp$sigma2[[ "idios" ]] ) )
      } else if( has.intercept( formula ) ) {
        start <- c( mean( yVec[ validObs ] ),
                    rep( log( var( yVec[ validObs ] ) / 2 ), 2 ) )
      } else {
        stop( "argument 'formula' seems to have neither an intercept",
              " nor any explanatory variables" )
      }
    } else {
      # OLS estimation for starting values
      ols <- lm.fit( xMat, yVec )
      start <- c( ols$coefficients,
                  log( sum( ols$residuals^2 ) / length( ols$residuals ) ) )
      ##################################################
      if(!is.null(const)) {
        if(const[[1]][1,apply(const[[1]], 2, function(x) sum(abs(x))>0)][1] > 0 ){
          start[apply(const[[1]], 2, function(x) sum(abs(x))>0)] = cen(start[apply(const[[1]], 2, function(x) sum(abs(x))>0)],1,Inf)
        }
        else if(const[[1]][1,apply(const[[1]], 2, function(x) sum(abs(x))>0)][1] < 0 ){
          start[apply(const[[1]], 2, function(x) sum(abs(x))>0)] = cen(start[apply(const[[1]], 2, function(x) sum(abs(x))>0)],-Inf,-1)
        }
      }
      ##################################################
    }
  } else {
    if( !is.numeric( start ) ) {
      stop( "argument 'start' must be numeric" )
    } else if( length( start ) != nParam ) {
      stop( "argument 'start' must have length ", nParam )
    }
  }
  
  if( isPanel ) {
    ## naming coefficients
    names( start ) <- c( colnames( xMat ), "logSigmaMu", "logSigmaNu" )
    
    ## Abscissae and weights for the Gauss-Hermite-Quadrature
    ghqPoints <- ghq( nGHQ, modified = FALSE )
    
    ## re-organize data 
    xArr <- array( NA, dim = c( nInd, nTime, ncol( xMat ) ) )
    yMat <- matrix( NA, nrow = nInd, ncol = nTime )
    for( i in 1:nTime ) {
      obsTime <- pIndex[[ 2 ]] == timeNames[ i ]
      xArr[ indNames %in% pIndex[[ 1 ]][ obsTime ], i, ] <- xMat[ obsTime, ]
      yMat[ indNames %in% pIndex[[ 1 ]][ obsTime ], i ] <- yVec[ obsTime ]
    }
    
    ## classify observations
    obsBelow <- yMat <= left & !is.na( yMat )
    obsAbove <- yMat >= right & !is.na( yMat )
    obsBetween <- !obsBelow & !obsAbove & !is.na( yMat )
    
    ## stop and return log likelihood values
    if( logLikOnly ) {
      result <- censRegLogLikPanel( beta = start,
                                    yMat = yMat, xArr = xArr, left = left, right = right, 
                                    nInd = nInd, nTime = nTime,
                                    obsBelow = obsBelow, obsBetween = obsBetween, obsAbove = obsAbove,
                                    nGHQ = nGHQ, ghqPoints = ghqPoints )
      return( result )
    }
    
    if( sum( obsBelow, na.rm = TRUE ) + sum( obsAbove, na.rm = TRUE ) == 0 ) {
      stop( "there are no censored observations" )
    }
    if( sum( obsBetween, na.rm = TRUE ) == 0 ) {
      stop( "there are no uncensored observations" )
    }
    
    ##################################################
    ## log likelihood function for panel data (incl. gradients)
    result <- maxLik( censRegLogLikPanel, start = start,
                      yMat = yMat, xArr = xArr, left = left, right = right, 
                      nInd = nInd, nTime = nTime,
                      obsBelow = obsBelow, obsBetween = obsBetween, obsAbove = obsAbove,
                      nGHQ = nGHQ, ghqPoints = ghqPoints, constraints = const,... )
    ##################################################
    
  } else {
    ## naming coefficients
    names( start ) <- c( colnames( xMat ), "logSigma" )
    
    ## classify observations
    obsBelow <- yVec <= left
    obsAbove <- yVec >= right
    obsBetween <- !obsBelow & !obsAbove
    
    ## stop and return log likelihood values
    if( logLikOnly ) {
      result <- censRegLogLikCross_wt( beta = start,
                                    yVec = yVec, xMat = xMat, left = left, right = right, 
                                    obsBelow = obsBelow, obsBetween = obsBetween, obsAbove = obsAbove, wt=wt )
      return( result )
    }
    
    if( sum( obsBelow, na.rm = TRUE ) + sum( obsAbove, na.rm = TRUE ) == 0 ) {
      stop( "there are no censored observations" )
    }
    if( sum( obsBetween, na.rm = TRUE ) == 0 ) {
      stop( "there are no uncensored observations" )
    }
    
    ##################################################
    ## log likelihood function for cross-sectional data
    result <- maxLik( censRegLogLikCross_wt, start = start,
                      yVec = yVec, xMat = xMat, left = left, right = right,
                      obsBelow = obsBelow, obsBetween = obsBetween, obsAbove = obsAbove,constraints = const,wt=wt,
                      ... )
    ##################################################
    
  }
  
  # return mean values of the explanatory variables
  result$xMean <- colMeans( xMat )
  
  # save and return the call
  result$call <- match.call()
  
  # return the model terms
  result$terms <- mt
  
  # save and return the number of oservations (in each category)
  result$nObs <- c( sum( obsBelow ), sum( obsBetween ), sum( obsAbove ) )
  result$nObs <- c( sum( result$nObs ), result$nObs )
  names( result$nObs ) <- c( "Total", "Left-censored", "Uncensored",
                             "Right-censored" )
  
  # return the degrees of freedom of the residuals
  result$df.residual <- unname( result$nObs[ 1 ] - length( coef( result ) ) )
  
  # return starting values
  result$start <- start
  
  # censoring points
  result$left <- left
  result$right <- right
  
  
  ##################################################
  # return X
  result$X <- xMat
  
  # return y
  result$y <- yVec
  
  # return R-squared & adjusted R-squared
  fitted.val = as.numeric(xMat%*%result$estimate[-(ncol(xMat)+1)]) # remove logSigma
  result$fitted.values.uncensored = fitted.val
  fitted.val[fitted.val>=right] = right # censored fitted value
  fitted.val[fitted.val<=left] = left # censored fitted value
  result$fitted.values = fitted.val
  mean.y = mean(yVec)
  nobs = length(yVec)
  residual.df = result$df.residual
  result$adj.r.squared <- 1 - var(yVec-fitted.val)*(nobs-1)/(var(yVec-mean.y)*residual.df)
  result$r.squared <- 1 - var(yVec-fitted.val)/var(yVec-mean.y)
  result$data <- data
  ##################################################
  class( result ) <- c( "censReg", class( result ) )
  return( result )
}

environment(censReg.adj) <- asNamespace('censReg')

AdjR2.tob = function(object){
  nobs = length(object$y)
  mean.y = mean(object$y)
  residual.df = object$df.residual
  fitted.val = as.numeric(as.matrix(object$X)%*%coef(object)[-length(coef(object))]) # remove logSigma
  fitted.val[fitted.val>=object$right] = object$right # censored fitted value
  fitted.val[fitted.val<=object$left] = object$left # censored fitted value
  return(1 - var(as.numeric(object$y)-fitted.val)*(nobs-1)/(var(as.numeric(object$y)-mean.y)*residual.df))
}