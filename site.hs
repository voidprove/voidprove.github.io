--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Data.Monoid (mappend)
import           Hakyll


--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "files/*" $ do
        route idRoute
        compile copyFileCompiler

    match "scripts/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "about.html" $ do
        route   idRoute
        compile $ getResourceBody
            >>= loadAndApplyTemplate "templates/default-no-title.html" (constField "about.html" "Yes" `mappend` defaultContext)
            >>= relativizeUrls

    match "about.html" $ version "indexPage" $ do
        route   $ constRoute "index.html"
        compile $ getResourceBody
            >>= loadAndApplyTemplate "templates/default-no-title.html" (constField "about.html" "Yes" `mappend` defaultContext)
            >>= relativizeUrls

    match "research-items/*" $ do
        compile $ pandocCompiler

    match "research.html" $ do
        route idRoute
        compile $ do
            researchItems <- recentFirst =<< loadAll "research-items/*"
            let researchCtx =
                    listField "researchItems" defaultContext (return researchItems) `mappend`
                    defaultContext
            getResourceBody
                >>= applyAsTemplate researchCtx
                >>= loadAndApplyTemplate "templates/default-no-title.html" (defaultContext `mappend` constField "research.html" "Yes")
                >>= relativizeUrls

    match "teaching.html" $ do
        route $ idRoute
        compile $ getResourceBody
            >>= loadAndApplyTemplate "templates/default-no-title.html" (defaultContext `mappend` constField "teaching.html" "Yes")
            >>= relativizeUrls

    -- match "posts/*" $ do
    --     route $ setExtension "html"
    --     compile $ pandocCompiler
    --         >>= loadAndApplyTemplate "templates/post.html"    postCtx
    --         >>= loadAndApplyTemplate "templates/default.html" postCtx
    --         >>= relativizeUrls

    -- create ["archive.html"] $ do
    --     route idRoute
    --     compile $ do
    --         posts <- recentFirst =<< loadAll "posts/*"
    --         let archiveCtx =
    --                 listField "posts" postCtx (return posts) `mappend`
    --                 constField "title" "Archives"            `mappend`
    --                 defaultContext

    --         makeItem ""
    --             >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
    --             >>= loadAndApplyTemplate "templates/default.html" archiveCtx
    --             >>= relativizeUrls

    -- match "index.html" $ do
    --     route idRoute
    --     compile $ do
    --         posts <- recentFirst =<< loadAll "posts/*"
    --         let indexCtx =
    --                 listField "posts" postCtx (return posts) `mappend`
    --                 constField "title" "Home"                `mappend`
    --                 defaultContext

    --         getResourceBody
    --             >>= applyAsTemplate indexCtx
    --             >>= loadAndApplyTemplate "templates/default.html" indexCtx
    --             >>= relativizeUrls

    -- match (fromList ["about.rst", "contact.markdown"]) $ do
    --     route   $ setExtension "html"
    --     compile $ pandocCompiler
    --         >>= loadAndApplyTemplate "templates/default.html" defaultContext
    --         >>= relativizeUrls

    match "templates/*" $ compile templateBodyCompiler


--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext
