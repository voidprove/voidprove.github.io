rm -rf cacml2024
cp -r ../cacml2024/_site .
mv _site cacml2024
git add -A
git commit -m "cacml2024 publish"
git push origin master:master