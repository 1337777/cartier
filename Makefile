
all : cartierSolution6.v.org cartierSolution7.v.org
	emacs --batch -l ./makeemacs_publish_init.el -f publish-worg

cartierSolution6.v.org : cartierSolution6.v
	sed -e '/^(\*\* # #$$/d' -e 's/# # \*\*)$$//' ./cartierSolution6.v > ./cartierSolution6.v.org

cartierSolution7.v.org : cartierSolution7.v
	sed -e '/^(\*\* # #$$/d' -e 's/# # \*\*)$$//' ./cartierSolution7.v > ./cartierSolution7.v.org

clean :
	rm cartierSolution6.v.org cartierSolution7.v.org
