package DeLP_GDPR.delp.examples;

import java.io.BufferedWriter;

import java.io.File;
import java.io.FileWriter;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Paths;

import org.tweetyproject.commons.ParserException;
import DeLP_GDPR.delp.examples.DeLPExample;
import DeLP_GDPR.delp.parser.DelpParser;
import DeLP_GDPR.delp.reasoner.DelpReasoner;
import DeLP_GDPR.delp.semantics.GeneralizedSpecificity;
import DeLP_GDPR.delp.syntax.DefeasibleLogicProgram;
import DeLP_GDPR.logics.fol.syntax.FolFormula;

/**
 * Shows how to parse and query a DeLP program.
 * 
 *
 */
public class DeLPExample {
	public static void main(String[] args) throws FileNotFoundException, ParserException, IOException{
		DelpParser parser = new DelpParser();
		DefeasibleLogicProgram delp = parser.parseBeliefBaseFromFile(DeLPExample.class.getResource("/resources/nonConsent").getFile());
		DelpReasoner reasoner = new DelpReasoner(new GeneralizedSpecificity());
		for (int i = 0; i < 10; i++) {
            long startTime = System.currentTimeMillis();

            // Perform the inference steps for the query here
            FolFormula query = (FolFormula) parser.parseFormula("ConsentCompliance(telehealthserviceserver, patient1)");
            System.out.println("Run " + (i + 1) + ": " + query + "\t" + reasoner.query(delp, query));

            long endTime = System.currentTimeMillis();
            long executionTime = endTime - startTime;
            //System.out.println("Run " + (i + 1) + ": Query execution time: " + executionTime + " milliseconds\n");
          System.out.println("Run " + (i + 1) + "time: " + executionTime + "\n");
		
		/*
		long startTime = System.currentTimeMillis();

		// Perform the inference steps for the query here
		FolFormula query = (FolFormula) parser.parseFormula("ConsentCompliance(telehealthserviceserver, patient1)");
		System.out.println(query + "\t" + reasoner.query(delp,query));

		long endTime = System.currentTimeMillis();
		long executionTime = endTime - startTime;
		System.out.println("Query execution time: " + executionTime + " milliseconds");
		/*		
		FolFormula query = (FolFormula) parser.parseFormula("ConsentCompliance(telehealthserviceserver, patient1)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		
		query = (FolFormula) parser.parseFormula("ConsentCompliance(telehealthserviceserver, patient2)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		
		query = (FolFormula) parser.parseFormula("ConsentCompliance(telehealthserviceserver, patient3)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		
		query = (FolFormula) parser.parseFormula("~ConsentCompliance(telehealthserviceserver, patient3)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		

		/*
		
		FolFormula query = (FolFormula) parser.parseFormula("information_disclosure(personal_data)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		
		FolFormula query = (FolFormula) parser.parseFormula("~Accountability(telehealthserviceserver, reportingbody)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		
		FolFormula query = (FolFormula) parser.parseFormula("FreelyGivenConsent(telehealthserviceserver, patient1)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		
		FolFormula query = (FolFormula) parser.parseFormula("ConsentCompliance(telehealthserviceserver, patient1)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		
		query = (FolFormula) parser.parseFormula("ConsentCompliance(telehealthserviceserver, patient2)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		
		query = (FolFormula) parser.parseFormula("ConsentCompliance(telehealthserviceserver, patient3)");
		System.out.println(query + "\t" + reasoner.query(delp,query));
		
		query = (FolFormula) parser.parseFormula("~ConsentCompliance(telehealthserviceserver, patient3)");
		System.out.println(query + "\t" + reasoner.query(delp,query));*/

		
		}	
		
	}

}