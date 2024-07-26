{-# LANGUAGE InstanceSigs #-}

import Prelude hiding (Monad, (>>=), return)

class Functor m => Monad m where
    return :: a -> m a
    (>>=)  :: m a -> (a -> m b) -> m b
    
    join :: m (m a) -> m a
    join = (>>= id)

instance Functor Maybe where
    fmap :: (a -> b) -> Maybe a -> Maybe b
    fmap _ Nothing  = Nothing
    fmap f (Just x) = Just (f x)

instance Monad Maybe where
    return :: a -> Maybe a
    return = Just

    (>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
    Nothing >>= _ = Nothing
    Just x  >>= f = f x

    join :: Maybe (Maybe a) -> Maybe a
    join Nothing         = Nothing
    join (Just Nothing)  = Nothing
    join (Just (Just x)) = Just x

-- Tests for the monad laws
leftUnit :: Eq (m a) => Monad m => m a -> Bool
leftUnit x = (join . fmap return) x == x

rightUnit :: Eq (m a) => Monad m => m a -> Bool
rightUnit x = (join . return) x == x

associativity :: Eq (m a) => Monad m => m (m (m a)) -> Bool
associativity x = (join . fmap join) x == (join . join) x

-- Example usage
main :: IO ()
main = do
    print $ leftUnit (Just 5)         -- Should be True
    print $ leftUnit (Nothing :: Maybe Int)  -- Should be True
    print $ rightUnit (Just 5)        -- Should be True
    print $ rightUnit (Nothing :: Maybe Int) -- Should be True
    print $ associativity (Just (Just (Just 5)))   -- Should be True
    print $ associativity (Just (Just Nothing))    -- Should be True
    print $ associativity (Just Nothing)           -- Should be True
    print $ associativity (Nothing :: Maybe (Maybe (Maybe Int))) -- Should be True
