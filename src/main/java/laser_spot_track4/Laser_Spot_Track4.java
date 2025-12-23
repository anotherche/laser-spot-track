package laser_spot_track4;

import org.scijava.util.AppUtils;

import net.imagej.updater.*;

import ij.*;
import ij.process.*;
import ij.gui.*;
import ij.io.*;
import java.io.*;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.Duration;
import java.time.Instant;

import com.drew.imaging.ImageMetadataReader;
import com.drew.metadata.Metadata;
import com.drew.metadata.exif.ExifSubIFDDirectory;

import java.awt.Rectangle;
import java.awt.AWTEvent;
import java.awt.Frame;

import ij.plugin.FolderOpener;
import ij.plugin.filter.*;
import ij.plugin.frame.Recorder;
import ij.measure.ResultsTable;
import java.awt.image.BufferedImage;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;
import java.util.jar.Attributes.Name;
import java.util.regex.Pattern;

import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;

import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.indexer.*;
import org.bytedeco.javacv.Java2DFrameUtils;
import org.bytedeco.opencv.opencv_core.Mat;
import org.bytedeco.opencv.opencv_core.Point;
import org.bytedeco.opencv.opencv_core.Size;

import static org.bytedeco.opencv.global.opencv_core.*;
import static org.bytedeco.opencv.global.opencv_imgproc.*;




/* This is a Maven project implementing an ImageJ plugin providing trackig of 
a spot moving in a field with 4 reference marks. It was created for automatization 
of tracking of laser spot reflected from the mirror attached to the end of
a needle-like crystal bending as a result of photomechanical effect (photobending).
Photobending is a phenomenon of crystal deformation caused by non-uniform 
crystal structure transformation due to photochemical reaction. 

Required input is a stack of timelapse images of the spot moving relative to the 
template picture with 4 marks located in the corners of a square.
The output is the time dependence of spot dislacement given in units of the square 
side length. Usage of the template with 4 marks allows to compensate for the effects 
of picture instability and view perspective.

The project uses ideas and code of 
1. Template Matching by Qingzong Tseng (based on opencv)
2. javacv (java interface to OpenCV) by Samuel Audet 
3. Exif Metadata Library by Drew Noakes
 */



public class Laser_Spot_Track4 implements PlugInFilter, DialogListener {

    ImagePlus imp, ref_Image, spot_ref, spot_tpl, holder_ref, mark1_ref, mark2_ref, mark3_ref, mark4_ref;

    GaussianBlur gaussianBlur;
    ImageStack stack;
    Rectangle spot_rect, holder_rect, mark1_rect, mark2_rect, mark3_rect, mark4_rect;
    Roi spot_roi,holder_roi, mark1_roi, mark2_roi, mark3_roi, mark4_roi;
    PointRoi proi_spot,proi_att,proi_mark1,proi_mark2,proi_mark3,proi_mark4;
    static final int matchMethodDefault = 5,
    		searchAreaDefault = 50,
    		templSizeDefault = 120;
    static final double markDistDefault = 100.0;
    static final boolean videoInputDefault = false;
    static final boolean autoSkipDefault = false;
    static final boolean matchIntensityDefault = true;
    static final boolean subPixelDefault = true;
    
    int method = matchMethodDefault, refSlice, sArea = searchAreaDefault, templSize = templSizeDefault, anStep=0;
    double seconds=0, timeStep=1.0, markDist = markDistDefault;
    Instant first_shot_time; 
    int width, height, refBitDepth, refX_spot, refY_spot, refX_att=0, refY_att=0,
    		refX_mark1, refY_mark1, 
    		refX_mark2, refY_mark2,
    		refX_mark3, refY_mark3,
    		refX_mark4, refY_mark4;
    double  disX_spot=0.0, disY_spot=0.0, disX_spot0=0.0, disY_spot0=0.0,
    		disX_mark1=0.0, disY_mark1=0.0, disX_mark10=0.0, disY_mark10=0.0, 
    		disX_mark2=0.0, disY_mark2=0.0, disX_mark20=0.0, disY_mark20=0.0,
    		disX_mark3=0.0, disY_mark3=0.0, disX_mark30=0.0, disY_mark30=0.0,
    		disX_mark4=0.0, disY_mark4=0.0, disX_mark40=0.0, disY_mark40=0.0,
    		dX_pix=0.0, dY_pix=0.0,
    		spotX0=0.0, spotY0=0.0,
    		x_abs, y_abs, 
    		dX=0.0, dY=0.0, dL=0.0;
    
    private static final Set<String> videoTypes = new HashSet<String>(java.util.Arrays.asList(
		     new String[] {"WEBM", "MKV", "VOB", "OGV", "OGG", "DRC", "MNG", "AVI", 
		    		 "MOV", "QT", "WMV", "YUV", "RM", "RMVB", "ASF", "AMV", "MP4", 
		    		 "M4P", "MPG", "MP2", "MPEG", "MPE", "MPV", "M2V", 
		    		 "M4V", "SVI", "3GP", "3G2", "MXF", "ROQ", "NSV", "FLV", "F4V", 
		    		 "F4P", "F4A", "F4B" }
		));
    
    private static final String pluginName = "Laser Spot Track";  
    private static final String INVALID_CHARACTERS = "[<>:\"/\\|?*]";
    
    /*
    
    double length_ini=0.0, cr_length, hord_ini,
    	   curvature_ini, curvature, 
    	   bending_angle_ini, bending_angle, 
    	   deflection_angle_ini, deflection_angle, 
    	   full_angle, full_angle_ini,
    	   initial_angle,
    	   deformation;
    double H0_x,H0_y;
    
*/
    
    
    ArrayList<Double> displacement_list, x_pix_list, y_pix_list, 
    				  time_list, spot_matchRes, attEnd_matchRes, 
    				  mark1_matchRes, mark2_matchRes, mark3_matchRes, mark4_matchRes ; 
    double displacement_min=0.0, displacement_max=0.0;
    double spot_mideal, att_mideal, mark1_mideal, mark2_mideal, mark3_mideal, mark4_mideal;
    
    ImagePlus plotImage;
    boolean folderMonitoring=true, updateTemplates=false, exifTime=true, autoSkip=autoSkipDefault, alwaysAutoSkip=autoSkipDefault;
    int autoSkipCounter=0, maxSArea=500;
    volatile WaitForUserDialog stopDlg=null, monitorDlg=null;
    volatile boolean trackFinished = false;
    
    
    
    //FloatProcessor result;
    ResultsTable rt;
    String projectName;
    int windowSizeX, windowSizeY, iniX, iniY;
    boolean subPixel = true;
    boolean matchIntensity = false;
    boolean showRT = true;
    boolean firstPoint = true, videoInput=videoInputDefault, stopPlugin=false, useTimeStamps=true, javacvInstalled = false;
	Roi refCropRoi = null;
	//Roi mid_refCropRoi = null;
	double[] matchThreshold=new double[]{0.1, 0.1, 0.05, 0.05, 0.2, 0.2};
	ImageWindow imgWindow;
	
	int movieFrameNum=0, previousFrameNum=0;
    double impliedFrameRate;
    ImagePlus prevMovieFrame;
    int trackStep = 1;
	


	private void setAltTimeMeasure()
	{
		GenericDialog gd = new GenericDialog("Default time step");
        gd.addMessage("The images do not have EXIF data.\n"
        		+ "A constant time step will be used to define creation time of every next image.\n"
        		+ "Change the default time step if necessary.");
        gd.addNumericField("Time step in seconds ", timeStep, 0);
        gd.showDialog();
        timeStep = gd.getNextNumber();
	}
	
	/*
	private boolean setStandardCrystalLength() {
		GenericDialog gd = new GenericDialog("Adjust crystal length");
        gd.addMessage("Set standard crystal length to adjust position of the attached end");
        gd.addMessage(String.format("Current crystal length: %.1f", length_ini));
        gd.addNumericField("Standard length in pixels ", length_ini, 0);
        gd.showDialog();
        if (gd.wasCanceled()) {
            return false;
        }
        
        double std_length = (int) gd.getNextNumber();
        refX_att = refX_spot + (int)(std_length*(refX_att - refX_spot)/length_ini);
        refY_att = refY_spot + (int)(std_length*(refY_att - refY_spot)/length_ini);
        H0_x=refX_spot-refX_att;
        H0_y=refY_spot-refY_att;
        length_ini=Math.sqrt(H0_x*H0_x+H0_y*H0_y);
        hord_ini= length_ini;
        
        full_angle_ini=Math.acos(H0_x/hord_ini);
        if (refY_spot>refY_att) full_angle_ini=-full_angle_ini;
        
        refX_mid = (refX_spot + refX_att)/2;
        refY_mid = (refY_spot + refY_att)/2;

        return true;

	}
*/
	
//    public int setup(String arg, ImagePlus imp) {
//    	
//    	int returnMask = NO_IMAGE_REQUIRED + DOES_8G + DOES_16 +  DOES_32 + DOES_RGB + STACK_REQUIRED;
//    	
//    	if (!CheckJavaCV("1.5", true, "opencv"))
//    	{
//    		return returnMask;
//    	}
//    	
//    	 this.imp = imp;
//         if (imp==null || imp.getStack()==null || imp.getStackSize()<2 || !imp.getStack().isVirtual()) {
//         	IJ.run("Image Sequence...");
//         	this.imp = IJ.getImage();
//         	
//         }
//         
//         return returnMask;
//    }
	
	
public int setup(String arg, ImagePlus imp) {
    	
		int returnMask = NO_IMAGE_REQUIRED + DOES_8G + DOES_16 +  DOES_32 + DOES_RGB + STACK_REQUIRED;
    	//IJ.run("Install JavaCV libraries", "select=[Install missing] opencv openblas");
    	
    	//if (!CheckJavaCV("opencv openblas ffmpeg"))
		javacvInstalled = checkJavaCV("1.5", true, "opencv");
		if (!javacvInstalled)
    	{
    		stopPlugin=true;
            return returnMask;
    	}
    	
		videoInput = (boolean) Prefs.get("laserspottrack.videoInput", videoInputDefault);
    	GenericDialog pluginMode = new GenericDialog(pluginName);
    	pluginMode.addMessage("Choose from the image source type - video (experimental) or time lapse series");
    	String[] sourceTypes = new String[]{"Time lapse series", "Video file"};
    	pluginMode.addRadioButtonGroup("Source Type", sourceTypes, 2, 1, (videoInput?"Video file":"Time lapse series"));
    	pluginMode.showDialog();
        if (pluginMode.wasCanceled()) {
        	stopPlugin=true;
            return returnMask;
        }
        videoInput = pluginMode.getNextRadioButton().equalsIgnoreCase("Video file");
        Prefs.set("laserspottrack.videoInput", videoInput);
        int openImpCount = WindowManager.getWindowCount();
        if (videoInput) {
        	
     	
        	ArrayList<String> videoStacks = new ArrayList<String>(0);
    		ArrayList<Integer> videoStackIDs = new ArrayList<Integer>(0);

        	int videoCount=0;
        	for (int srcCnt = 0; srcCnt < openImpCount; srcCnt++) {
        		ImagePlus openImp = WindowManager.getImage(srcCnt+1);
        		if (openImp.getStack()!=null 
        				&& openImp.getStack().getSize()>1 
        				&& openImp.getStack().isVirtual()
        				&& (openImp.getProperty("stack_source_type")!=null &&
        				     openImp.getProperty("stack_source_type").toString().equals("ffmpeg_frame_grabber"))){
        			videoStacks.add(openImp.getTitle());
        			videoStackIDs.add(openImp.getID());
        			videoCount++;

        		}
        		
        	}
        	
        	if (videoCount>0){

            	if (videoCount==1 && WindowManager.getCurrentImage().getID()==videoStackIDs.get(0)){
            		this.imp = WindowManager.getImage(videoStackIDs.get(0));
    				WindowManager.setCurrentWindow(this.imp.getWindow());
    				return returnMask;
            	}
        		GenericDialog gd = new GenericDialog(pluginName);
        		gd.addMessage("Select the video stack or press Cancel to open another video");
        		gd.addChoice("List of open video stacks", videoStacks.toArray(new String[0]), videoStacks.get(0));
        		gd.showDialog();
    			if (!gd.wasCanceled()) {
    				this.imp = WindowManager.getImage(videoStackIDs.get(gd.getNextChoiceIndex()));
    				WindowManager.setCurrentWindow(this.imp.getWindow());
    				return returnMask;
    			}
        	} 


        	
        	String videoReadCommand = "Using FFmpeg...";
        	Hashtable table = Menus.getCommands();
    		String className = (String)table.get(videoReadCommand);
    		if (className==null) {
    			videoReadCommand = "Compressed video";
    			className = (String)table.get(videoReadCommand);
    			if (className==null) {
    				videoReadCommand = "Import Movie Using FFmpeg...";
        			className = (String)table.get(videoReadCommand);
        			if (className==null)
        				IJ.showMessage("FFmpeg_Video plugin is necessary to import compressed video. \nIt can be intalled from the update site http://sites.imagej.net/VideoImportExport.");
    			}
    		}
    		
    		OpenDialog	od = new OpenDialog("Open Video File", "");


    		if (od.getFileName() != null) {
    			//IJ.run("Using FFmpeg...", "open=["+od.getPath()+"] importquiet=true");
    			IJ.run(videoReadCommand, "open=["+od.getPath()+"]");
    			this.imp = WindowManager.getCurrentImage();
    		} else {
    			stopPlugin=true;
    			return returnMask;
    		}
    		
    		
        	//this.imp = WindowManager.getCurrentImage();
        	if (this.imp == null || this.imp.getProperty("stack_source_type")==null ||
        			!this.imp.getProperty("stack_source_type").toString().equals("ffmpeg_frame_grabber")) {
    			stopPlugin=true;
    			return returnMask;
    		}
        	
        } else {
        	ArrayList<String> imgStacks = new ArrayList<String>(0);
    		ArrayList<Integer> imgStackIDs = new ArrayList<Integer>(0);

        	int seqCount=0;
        	for (int srcCnt = 0; srcCnt < openImpCount; srcCnt++) {
        		ImagePlus openImp = WindowManager.getImage(srcCnt+1);
        		

        		if (openImp.getStack()!=null 
        				&& openImp.getStack().getSize()>1 
        				&& openImp.getStack().isVirtual()
        				&& (openImp.getProperty("stack_source_type")==null ||
        				     (openImp.getProperty("stack_source_type")!=null &&
        				     !openImp.getProperty("stack_source_type").toString().equals("ffmpeg_frame_grabber")))){
        			imgStacks.add(openImp.getTitle());
        			imgStackIDs.add(openImp.getID());
        			seqCount++;
        		}
        		
        	}
        	if (seqCount>0){
        		
            	if (seqCount==1 && WindowManager.getCurrentImage().getID()==imgStackIDs.get(0)){
            		this.imp = WindowManager.getImage(imgStackIDs.get(0));
    				WindowManager.setCurrentWindow(this.imp.getWindow());
    				return returnMask;
            	}
        		GenericDialog gd = new GenericDialog(pluginName);
        		gd.addMessage("Select image sequence stack or press Cancel to open another stack");
        		gd.addChoice("List of open virtual stacks", imgStacks.toArray(new String[0]), imgStacks.get(0));
        		gd.showDialog();
    			if (!gd.wasCanceled()) {
    				this.imp = WindowManager.getImage(imgStackIDs.get(gd.getNextChoiceIndex()));
    				WindowManager.setCurrentWindow(this.imp.getWindow());
    				
    				return returnMask;
    			}
        	} 
        	
        	
        	
        		OpenDialog	od = new OpenDialog("Select first file in the sequence", "");


        		if (od.getFileName() != null) {
        			
        			String sequencePath = od.getPath();
        			String firstFileName = od.getFileName();
        			String extension = "";
        			int i = firstFileName.lastIndexOf('.');
        			if (i > 0 && i < firstFileName.length() - 1) {
        			    extension = firstFileName.substring(i+1);
        			    if (videoTypes.contains(extension.toUpperCase())) {
        			    	IJ.showMessage("Error", "It seems that a video file is selected instead of image file.");
        			    	stopPlugin=true;
                			return returnMask;
        			    }
        			} else {
            			stopPlugin=true;
            			return returnMask;
            		}
        			File[] fileList = (new File(od.getDirectory())).listFiles();
        			ArrayList<String> stackFiles = new ArrayList<String>(0);
	            	int firstFile=0;

	            	for (i = 0; i < fileList.length; i++){
	            		if (fileList[i].isFile() && fileList[i].getName().contains(extension)){
	            			stackFiles.add(fileList[i].getName());
	            		}
	            	}
	            	if (stackFiles.size()<2){
	            		stopPlugin=true;
	        			return returnMask;
	            	} else {
	            		stackFiles.sort(null);//(String::compareToIgnoreCase);
	            		firstFile=stackFiles.indexOf(firstFileName) + 1;
	            	}
	            	if (firstFile==0) {
	        			stopPlugin=true;
	        			return returnMask;
	        		}
	            	
        			IJ.run("Image Sequence...", "open=["+sequencePath+"] starting="+firstFile+" file="+extension+" sort use");
        			this.imp = IJ.getImage();
        			FileInfo fi = new FileInfo();
        			fi.fileName = firstFileName;
        			fi.directory = od.getDirectory();
        			
        			this.imp.setFileInfo(fi);
        			
        		} else {
        			stopPlugin=true;
        			return returnMask;
        		}
        		

        	
        }
        
        return returnMask;
    }

    
	public void run(ImageProcessor ip) {

		if (stopPlugin) {
			if (javacvInstalled) IJ.showMessage("Error", "No source chosen. Stopping.");
			return;
		}
		
		imgWindow=imp.getWindow();
		
        stack = imp.getStack();
        if (stack.size()<2)  {
        	IJ.showMessage("Error", "There is only 1 slice in the stack.\nNothing to track.");
            return;
        }
        
        if (!videoInput && !stack.isVirtual()) {
        	IJ.showMessage("Error", "Only virtual stacks are supported");
            return;
        }
        
        
        
        if (videoInput){
        	
        	boolean fpsDetected=true;
        	if (imp.getProperty("video_fps")!=null){
        		impliedFrameRate=Double.parseDouble(imp.getProperty("video_fps").toString());//((FFmpeg_FrameReader)stack).getFrameRate();
        	} else {
        		impliedFrameRate=1.0;
        		fpsDetected=false;
        	}
        	
        	
        	GenericDialog gd = new GenericDialog(pluginName);
        	gd.addMessage("Please chose the method of getting the timestamp info\n"
        			+ "\"Frame timestapm\" (default) is useful in case of variable frame rate;\n"
        			+ "\"Calculate from frame rate\" works with constant frame rate video and allows to change the frame rate value.");
        	gd.addRadioButtonGroup("Timestamp source", new String[]{"Frame timestapm", "Calculate from frame rate"}, 2, 1, "Frame timestapm");
        	String fps_detected = String.format("%.3f", impliedFrameRate);
        	if (fpsDetected){
        		gd.addMessage("Frame rate of the video is determined as: "+ fps_detected + " fps.\n"
        			+ "You may redefine the frame rate beneath.");
        	} else {
        		gd.addMessage("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n"+
        	"Frame rate of the video cannot be determined. It is arbitrarily set to 1 fps\n"
            			+ "You may redefine the frame rate beneath.\n"+
        				  "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
        	}
        	gd.addNumericField("Change frame rate to", impliedFrameRate, 3);

        	gd.showDialog();
        	if (gd.wasCanceled()) {
        		IJ.showMessage("Plugin is canceled.");
        		return;
        	}

        	useTimeStamps=gd.getNextRadioButton().equalsIgnoreCase("Frame timestapm");
        	impliedFrameRate = gd.getNextNumber();
        	if (!useTimeStamps && (impliedFrameRate==Double.NaN || impliedFrameRate<=0)){
        		IJ.showMessage("Wrong frame rate specified. Stopping plugin.");
        		return;
        	}
        }
        
        
        
        
        displacement_list = new ArrayList<Double>();
        x_pix_list = new ArrayList<Double>();
        y_pix_list = new ArrayList<Double>();
        
        time_list = new ArrayList<Double>();
        
        spot_matchRes = new ArrayList<Double>();
        mark1_matchRes = new ArrayList<Double>();
        mark2_matchRes = new ArrayList<Double>();
        mark3_matchRes = new ArrayList<Double>();
        mark4_matchRes = new ArrayList<Double>();
        
        attEnd_matchRes = new ArrayList<Double>();
        
        
        
        PlotWindow.noGridLines = false; // draw grid lines
       
        
        
        width = imp.getWidth();
        height = imp.getHeight();
        refBitDepth = imp.getBitDepth();
		disX_spot=0.0;
		disY_spot=0.0;
		
		
		

        if (!getUserParameters()) return;
        
        
        Overlay ov;
		ImageProcessor ip_tmp;
        
        ov = new Overlay();
        imp.setOverlay(ov);
        
        refSlice = imp.getCurrentSlice();
        ref_Image = new ImagePlus(stack.getSliceLabel(refSlice), stack.getProcessor(refSlice));
        
        
        
		IJ.setTool("point");
        new WaitForUserDialog("Laser_Spot_Track4", "Select a point in the center of the spot...\nthen press OK.").show();
        
        proi_spot = (PointRoi)imp.getRoi();
        if (proi_spot!=null) {
        refX_spot=proi_spot.getPolygon().xpoints[0];
        refY_spot=proi_spot.getPolygon().ypoints[0];
        } else {
        	IJ.showMessage("Error", "point ROI needed");
            return;
        }
        
        int d1 = refX_spot, d2 = width - refX_spot, d3 = refY_spot, d4 = height - refY_spot;
        int dmin = Math.min(Math.min(d1, d2), Math.min(d3, d4));
        if (dmin<=templSize/2+sArea+1)
        {
        	IJ.showMessage("Error", "Search point is to close to the edge.\nReduce template rectangle size on the first dialog.");
            return;
        }
        
        int rect_half_size=templSize/2;
                             
		proi_spot.setPointType(3);
        ov.addElement(proi_spot);
        imp.setOverlay(ov);
        
        spot_roi=new Roi(refX_spot-rect_half_size,refY_spot-rect_half_size,2*rect_half_size,2*rect_half_size);
        ref_Image.setRoi(spot_roi);
        
        spot_rect = spot_roi.getBounds();
        
		spot_ref = ref_Image.crop();
		
        if (matchIntensity) {
        	ImageConverter ic = new ImageConverter(spot_ref);
        	ic.convertToGray32();
        }
        
        ip_tmp=spot_ref.getProcessor();
        gaussianBlur = new GaussianBlur();
        gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
        refCropRoi =  spot_roi; //new Roi((int)(spot_ref.getWidth()*0.15), (int)(spot_ref.getHeight()*0.15), (int)(spot_ref.getWidth()*0.7), (int)(spot_ref.getHeight()*0.7));
	
        
        
      
        
        
		imp.killRoi();
		
		
		IJ.setTool("point");
        new WaitForUserDialog("Laser_Spot_Track4", "Select a point in the center of the Mark1...\nthen press OK.").show();
        
        proi_mark1 = (PointRoi)imp.getRoi();
        if (proi_mark1!=null) {
        refX_mark1=proi_mark1.getPolygon().xpoints[0];
        refY_mark1=proi_mark1.getPolygon().ypoints[0];
        } else {
        	IJ.showMessage("Error", "point ROI needed");
            return;
        }
        
        proi_mark1.setPointType(3);
        ov.addElement(proi_mark1);
        imp.setOverlay(ov);
        
        mark1_roi=new Roi(refX_mark1-rect_half_size,refY_mark1-rect_half_size,2*rect_half_size,2*rect_half_size);
        ref_Image.setRoi(mark1_roi);
        
        mark1_rect = mark1_roi.getBounds();
        
		mark1_ref = ref_Image.crop();
        if (matchIntensity) {
        	ImageConverter ic = new ImageConverter(mark1_ref);
        	ic.convertToGray32();
        }
        
        ip_tmp=mark1_ref.getProcessor();
        gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
        mark1_mideal= doMatch_test(mark1_ref.getProcessor(),(method==0?2:method));
        
        imp.killRoi();
		
		
		IJ.setTool("point");
        new WaitForUserDialog("Laser_Spot_Track4", "Select a point in the center of the Mark2...\nthen press OK.").show();
        
        proi_mark2 = (PointRoi)imp.getRoi();
        if (proi_mark2!=null) {
        refX_mark2=proi_mark2.getPolygon().xpoints[0];
        refY_mark2=proi_mark2.getPolygon().ypoints[0];
        } else {
        	IJ.showMessage("Error", "point ROI needed");
            return;
        }
        
        proi_mark2.setPointType(3);
        ov.addElement(proi_mark2);
        imp.setOverlay(ov);
        
        mark2_roi=new Roi(refX_mark2-rect_half_size,refY_mark2-rect_half_size,2*rect_half_size,2*rect_half_size);
        ref_Image.setRoi(mark2_roi);
        
        mark2_rect = mark2_roi.getBounds();
        
		mark2_ref = ref_Image.crop();
        if (matchIntensity) {
        	ImageConverter ic = new ImageConverter(mark2_ref);
        	ic.convertToGray32();
        }
        
        ip_tmp=mark2_ref.getProcessor();
        gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
        mark2_mideal= doMatch_test(mark2_ref.getProcessor(),(method==0?2:method));
        imp.killRoi();
		
		
		IJ.setTool("point");
        new WaitForUserDialog("Laser_Spot_Track4", "Select a point in the center of the Mark3...\nthen press OK.").show();
        
        proi_mark3 = (PointRoi)imp.getRoi();
        if (proi_mark3!=null) {
        refX_mark3=proi_mark3.getPolygon().xpoints[0];
        refY_mark3=proi_mark3.getPolygon().ypoints[0];
        } else {
        	IJ.showMessage("Error", "point ROI needed");
            return;
        }
        
        proi_mark3.setPointType(3);
        ov.addElement(proi_mark3);
        imp.setOverlay(ov);
        
        mark3_roi=new Roi(refX_mark3-rect_half_size,refY_mark3-rect_half_size,2*rect_half_size,2*rect_half_size);
        ref_Image.setRoi(mark3_roi);
        
        mark3_rect = mark3_roi.getBounds();
        
		mark3_ref = ref_Image.crop();
        if (matchIntensity) {
        	ImageConverter ic = new ImageConverter(mark3_ref);
        	ic.convertToGray32();
        }
        
        ip_tmp=mark3_ref.getProcessor();
        gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
        mark3_mideal= doMatch_test(mark3_ref.getProcessor(),(method==0?2:method));
        imp.killRoi();
		
		
		IJ.setTool("point");
        new WaitForUserDialog("Laser_Spot_Track4", "Select a point in the center of the Mark4...\nthen press OK.").show();
        
        proi_mark4 = (PointRoi)imp.getRoi();
        if (proi_mark4!=null) {
        refX_mark4=proi_mark4.getPolygon().xpoints[0];
        refY_mark4=proi_mark4.getPolygon().ypoints[0];
        } else {
        	IJ.showMessage("Error", "point ROI needed");
            return;
        }
        
        proi_mark4.setPointType(3);
        ov.addElement(proi_mark4);
        imp.setOverlay(ov);
        
        mark4_roi=new Roi(refX_mark4-rect_half_size,refY_mark4-rect_half_size,2*rect_half_size,2*rect_half_size);
        ref_Image.setRoi(mark4_roi);
        
        mark4_rect = mark4_roi.getBounds();
        
		mark4_ref = ref_Image.crop();
        if (matchIntensity) {
        	ImageConverter ic = new ImageConverter(mark4_ref);
        	ic.convertToGray32();
        }
        
        ip_tmp=mark4_ref.getProcessor();
        gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
        mark4_mideal= doMatch_test(mark4_ref.getProcessor(),(method==0?2:method));
		
        int defaultPrecision = Analyzer.getPrecision();
        Analyzer.setPrecision(6);    
		if (showRT) {
            
        	
        	
        	rt = new ResultsTable();
        	rt.showRowNumbers(false);
        	
            
//            rt.setDecimalPlaces(2, 2);
//			rt.setDecimalPlaces(3, 2);
//			rt.setDecimalPlaces(4, 2);
//			rt.setDecimalPlaces(5, 2);
//			rt.setDecimalPlaces(6, 2);
			
			
			rt.show("Results");
            //rt.showRowNumbers(false);

        }
        
		FileInfo fi = null;
        String directory = "";
        String name = "";
        
        fi = imp.getOriginalFileInfo();
        directory = fi.directory;
        name = stack.getSliceLabel(refSlice);
        
        String firstShotPath =  Paths.get(directory, name).toString();
    	first_shot_time = getShotTime(firstShotPath, refSlice);
    	if (first_shot_time==null) exifTime=false;
		
		//calcDisplacement();
    	analyseSlice(refSlice, stack.getProcessor(refSlice));
		
		
		
		if (showRT) {
            rt.incrementCounter();
            rt.addValue("Time", 0);
            rt.addValue("Frame", "" + rt.getCounter());
            //rt.addValue("File", stack.getSliceLabel(refSlice));
            if (videoInput) rt.addValue("File", imp.getTitle() + ":" +stack.getSliceLabel(refSlice).replaceAll(" ", ""));
            else rt.addValue("File", stack.getSliceLabel(refSlice));
            rt.addValue("dX_pix", dX_pix);
            rt.addValue("dY_pix", dY_pix);
            rt.addValue("X_abs", x_abs);
            rt.addValue("Y_abs", y_abs);
            rt.addValue("dL", dL);
            
			
//			rt.setDecimalPlaces(2, 2);
//			rt.setDecimalPlaces(3, 2);
//			rt.setDecimalPlaces(4, 2);
//			rt.setDecimalPlaces(5, 2);
//			rt.setDecimalPlaces(6, 2);
			
			rt.show("Results");
            //rt.showRowNumbers(false);
            //IJ.log("colnumber - " + (rt.getLastColumn() +  1));
            
            
        }

		imp.deleteRoi();
		ref_Image.deleteRoi();
		
		displacement_list.add(dL);
		x_pix_list.add(refX_spot+disX_spot-disX_mark1);
		y_pix_list.add(refY_spot+disY_spot-disY_mark1);
       
        time_list.add(0.0);
        
        
        
		
                                                    // new plot window
        plotImage = new ImagePlus("Displacement plot", (new Plot("Displacement plot","Time, s","Displacement, mm")).getProcessor());
        plotImage.show();
        
        
        
        
        Thread StopThread = new Thread(new Runnable()
		{
        	@Override
			public void run() 
			{
        	    boolean continueTrack = true;
        	    String closeMsg = (videoInput ? "Change track step or Stop the track" : "Close this message to stop the track");
        	    WaitForUserDialog dlg = new WaitForUserDialog("Tracking in progress...", closeMsg);
        		dlg.setName("StopThread");
        		stopDlg=dlg;
        		String[] trackOptions = new String[] {"Track every frame", "Track by 0.2 sec", "Track by 0.5 sec", "Track by 1 sec"};
        		while (continueTrack) {
        		    continueTrack = false;
        		    dlg.show();
        		    if (!trackFinished && videoInput) {
        		        GenericDialog gDialog = new GenericDialog(pluginName + " - confirm stop or change settings");
        		        gDialog.addMessage("Press OK to contiune track with new settings\n or press Cancel to stop tracking.");
        		        gDialog.addRadioButtonGroup("Select frame decimation option", trackOptions, 4, 1, trackOptions[0]);
        		        gDialog.showDialog();
        		        if (gDialog.wasCanceled()) {
        		            continueTrack = false;
        	            } else {
        	                continueTrack = true;
        	                String selectedOptionString = gDialog.getNextRadioButton();
        	                if (selectedOptionString.equalsIgnoreCase(trackOptions[1])) trackStep = (int)(impliedFrameRate * 0.2);
        	                else if (selectedOptionString.equalsIgnoreCase(trackOptions[2])) trackStep = (int)(impliedFrameRate * 0.5);
        	                else if (selectedOptionString.equalsIgnoreCase(trackOptions[3])) trackStep = (int) impliedFrameRate;
        	                else trackStep = 1;
        	                
        	            }
        		    }
        		}
        		
				
			}
		});
		StopThread.start();	
        
		
		trackFinished = false;
        for (int i = refSlice + 1; i < stack.getSize() + 1; i+=trackStep) {    
        	
        	if (!StopThread.isAlive()) {
        		//new WaitForUserDialog("Laser Spot Track4", "The track is finished.").show();
        		saveResults(directory);
        		Analyzer.setPrecision(defaultPrecision);
        		return;
        	}
        	
        	Opener opener=null;  
			String imageFilePath="";
			
			ImagePlus imp_new=null;
        	
        	if (!videoInput){
				opener = new Opener();  
				imageFilePath = Paths.get(directory, stack.getSliceLabel(i)).toString();
				imp_new = opener.openImage(imageFilePath);
			}
        	
			if (videoInput || ((new File(imageFilePath)).isFile() 
					&& imp_new!=null 
					&& imp_new.getWidth()==width 
					&& imp_new.getHeight()==height 
					&& imp_new.getBitDepth()==refBitDepth)){

				
					double  tmp_disX_spot=disX_spot,
							tmp_disY_spot=disY_spot,
							tmp_disX_mark1=disX_mark1,
							tmp_disY_mark1=disY_mark1,
							tmp_disX_mark2=disX_mark2,
							tmp_disY_mark2=disY_mark2,
							tmp_disX_mark3=disX_mark3,
							tmp_disY_mark3=disY_mark3,
							tmp_disX_mark4=disX_mark4,
							tmp_disY_mark4=disY_mark4;
							
				    int matchresult = analyseSlice(i, stack.getProcessor(i));
					if (matchresult==1) {
							disX_spot=tmp_disX_spot;
							disY_spot=tmp_disY_spot;
							disX_mark1=tmp_disX_mark1;
							disY_mark1=tmp_disY_mark1;
							disX_mark2=tmp_disX_mark2;
							disY_mark2=tmp_disY_mark2;
							disX_mark3=tmp_disX_mark3;
							disY_mark3=tmp_disY_mark3;
							disX_mark4=tmp_disX_mark4;
							disY_mark4=tmp_disY_mark4;
							
						if (videoInput) i += (int)impliedFrameRate;
						continue;
					}
					if (matchresult==2) {
						
						if (stopDlg!=null) {
				        	stopDlg.close();
				        	try {
								StopThread.join();
							} catch (InterruptedException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
				        }
						saveResults(directory);
						Analyzer.setPrecision(defaultPrecision);
						return;
					}
		            
		            
		            
		            if (showRT) {
		            	rt.incrementCounter();
		            	
		                rt.addValue("Time", seconds);
		                rt.addValue("Frame", "" + rt.getCounter());
		                if (videoInput) rt.addValue("File", imp.getTitle() + ":" +stack.getSliceLabel(i).replaceAll(" ", ""));
		                else rt.addValue("File", stack.getSliceLabel(refSlice));
		                rt.addValue("dX_pix", dX_pix);
		                rt.addValue("dY_pix", dY_pix);
		                rt.addValue("X_abs", x_abs);
		                rt.addValue("Y_abs", y_abs);
		                rt.addValue("dL", dL);
		               
		                
//						rt.setDecimalPlaces(2, 2);
//						rt.setDecimalPlaces(3, 2);
//						rt.setDecimalPlaces(4, 2);
//						rt.setDecimalPlaces(5, 2);
//						rt.setDecimalPlaces(6, 2);
						
						
		
		                rt.show("Results");
		                //rt.showRowNumbers(false);
		                
		                
		                
		                
		            }
					displacement_list.add(dL);
					
		            
		            time_list.add(seconds);
		            
		            if (dL>displacement_max) displacement_max=dL;
		            if (dL<displacement_min) displacement_min=dL;
		            
		            
		            double y_height=displacement_max-displacement_min;
		            if (y_height==0.0) y_height=1.0;
		            double y_min=displacement_min-0.1*y_height,
		            	   y_max=displacement_max+0.1*y_height;
		            Plot plot1 = new Plot("Displacement Plot","Time, s","Displacement, mm");
		            plot1.setLimits(0, seconds, y_min, y_max);
		    		plot1.addPoints(time_list, displacement_list, Plot.LINE);
		    		ImageProcessor plotIp = plot1.getProcessor();
		    		plotImage.setProcessor(null, plotIp);
		    		
		    		
		    		
        	} else {
        		stack.deleteSlice(i--);
        		imp.setStack(stack);
        	}
            
        }
       
        trackFinished = true;
        
        if (stopDlg!=null) {
            stopDlg.close();
        	try {
				StopThread.join();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
        }
        	
        if (videoInput){
//     	   if (saveFlatten){
//            	
//            	//saveFlattenFrames(((FFmpeg_FrameReader)stack).getDirectory() + "flatten"+File.separatorChar, 0, true);
//     		   saveFlattenFrames(imp.getOriginalFileInfo().directory + "flatten"+File.separatorChar, 0, true);
//            }
            //new WaitForUserDialog("Laser Spot Tracking", "The track is finished.").show();
            saveResults(directory);
            Analyzer.setPrecision(defaultPrecision);
        	return;
        }
       
        
        GenericDialog gd = new GenericDialog("Monitor for additional images");
        gd.addMessage("Do you want to check/monitor the folder for additional images?");
        gd.showDialog();
        if (gd.wasCanceled()) {
            saveResults(directory);
            Analyzer.setPrecision(defaultPrecision);
            return;
        }
        
        trackFinished = false;
        Thread monitorThread = new Thread(new Runnable()
		{
        	@Override
			public void run() 
			{
        		WaitForUserDialog dlg = new WaitForUserDialog("Waiting for new images...", "The folder will be monitored for new images until the dialog is closed");
				
				
        		dlg.setName("MonitorThread");
        		monitorDlg=dlg;
        		dlg.show();
				
			}
		});
		monitorThread.start();	
		
		synchronized (this){
			try {
				this.wait(2000);
				} catch (InterruptedException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
		}
			
        while (monitorThread.isAlive()) {
        	
            
        	
            	File[] fileList = (new File(directory)).listFiles();
            	if (fileList != null) {
            		
	
	            	// Exclude directories
	            	String[] tmplist = new String[fileList.length];
	            	
	            	
	            	int c = 0;
	            	for (int i = 0; i < fileList.length; i++)
	            		if (fileList[i].isFile())
	            			tmplist[c++] = fileList[i].getName();
	            	if (c>0) {
		            	String[] list = new String[c];
		            	for (int i = 0; i < c; i++) 
		            		list[i] = tmplist[i];
		            	
		
		            	// Now exclude non-image files as per the ImageJ FolderOpener
		            	FolderOpener fo = new FolderOpener();
		            	list = fo.trimFileList(list);
		            	if (list != null && list.length>0){
			            	
			            	VirtualStack vstack = (VirtualStack)imp.getStack();
			           
			            	if (list.length > vstack.getSize()) {
			            		String[] imageList = fo.sortFileList(list);
			            		String LastSliceName = vstack.getSliceLabel(imp.getCurrentSlice());//vstack.getSliceLabel(vstack.getSize());
			            		int foundPosition=0;
			            		boolean filefound=false;
			            		for (foundPosition = imageList.length-1; foundPosition>= 0; foundPosition--)
			            		{
			            			if (LastSliceName.equalsIgnoreCase(imageList[foundPosition])){
			            				filefound=true;
			            				break;
			            			}
			            		}
			            		if (filefound)	
			            				for (int j = foundPosition+1; j<imageList.length;j++)
			            				{
			            					
			            					if (!monitorThread.isAlive()) break;
			            					
			            					Opener opener = new Opener();  
			            					String imageFilePath = Paths.get(directory, imageList[j]).toString();
			            					ImagePlus imp_new = opener.openImage(imageFilePath);
			            					if (imp_new!=null 
			            							&& imp_new.getWidth()==width 
			            							&& imp_new.getHeight()==height 
			            							&& imp_new.getBitDepth()==refBitDepth){
			            						
			            		        		vstack.addSlice(imageList[j]);
				            					
				            					imp.setStack(vstack);
				            					
				            					imp.setSlice(vstack.getSize());
				            					
				            					
				            					double  tmp_disX_spot=disX_spot,
				            							tmp_disY_spot=disY_spot,
				            							tmp_disX_mark1=disX_mark1,
				            							tmp_disY_mark1=disY_mark1,
				            							tmp_disX_mark2=disX_mark2,
				            							tmp_disY_mark2=disY_mark2,
				            							tmp_disX_mark3=disX_mark3,
				            							tmp_disY_mark3=disY_mark3,
				            							tmp_disX_mark4=disX_mark4,
				            							tmp_disY_mark4=disY_mark4;
				            				    			            					
				            					int matchresult = analyseSlice(vstack.getSize(),imp_new.getProcessor());
				            						
				            						if (matchresult==1) {
				            							disX_spot=tmp_disX_spot;
				            							disY_spot=tmp_disY_spot;
				            							disX_mark1=tmp_disX_mark1;
				            							disY_mark1=tmp_disY_mark1;
				            							disX_mark2=tmp_disX_mark2;
				            							disY_mark2=tmp_disY_mark2;
				            							disX_mark3=tmp_disX_mark3;
				            							disY_mark3=tmp_disY_mark3;
				            							disX_mark4=tmp_disX_mark4;
				            							disY_mark4=tmp_disY_mark4;
				            							//disX_mid=tmp_disX_mid;
				            							//disY_mid=tmp_disY_mid;
				            						continue;
				            						}
				            						if (matchresult==2) {
				            							if (monitorDlg!=null) {
				            							    trackFinished = true;
				            					        	monitorDlg.close();
				            					        	try {
				            									monitorThread.join();
				            								} catch (InterruptedException e) {
				            									// TODO Auto-generated catch block
				            									e.printStackTrace();
				            								}
				            					        }
				            							return;
				            						}
				            						
					            					//double ddx=disX_spot-disX_holder, ddy=disY_spot-disY_holder;
					            		            
					            		            if (showRT) {
					            		            	rt.incrementCounter();
					            		            	rt.addValue("Time", seconds);
					            		            	rt.addValue("Frame", "" + rt.getCounter());
					            		            	rt.addValue("File", stack.getSliceLabel(vstack.getSize()));
					            		            	rt.addValue("dX_pix", dX_pix);
					            		                rt.addValue("dY_pix", dY_pix);
					            		                rt.addValue("X_abs", x_abs);
					            		                rt.addValue("Y_abs", y_abs);
					            		                rt.addValue("dL", dL);
					            		               
					            		                
//						            						rt.setDecimalPlaces(2, 2);
//						            						rt.setDecimalPlaces(3, 2);
//						            						rt.setDecimalPlaces(4, 2);
//						            						rt.setDecimalPlaces(5, 2);
//						            						rt.setDecimalPlaces(6, 2);
					            						
					            		                
					            		                rt.show("Results");
					            		                //rt.showRowNumbers(false);
					            		                
					            		               
					            		                
					            		            }
					            		            
					            					displacement_list.add(dL);
					            					
					            		            
					            		            time_list.add(seconds);
					            		            
					            		            if (dL>displacement_max) displacement_max=dL;
					            		            if (dL<displacement_min) displacement_min=dL;
					            		            
					            		            
					            		            
					            		            double y_height=displacement_max-displacement_min;
					            		            if (y_height==0.0) y_height=1.0;
					            		            double y_min=displacement_min-0.1*y_height,
					            		            	   y_max=displacement_max+0.1*y_height;
					            		            Plot plot1 = new Plot("Displacement Plot","Time, s","Displacement");
					            		            plot1.setLimits(0, seconds, y_min, y_max);
					            		    		plot1.addPoints(time_list, displacement_list, Plot.LINE);
					            		    		ImageProcessor plotIp = plot1.getProcessor();
					            		    		plotImage.setProcessor(null, plotIp);
					            		    		
					            		    		
					            		    		
					            		     		
					            		     		
			            					}
			            				}
			            			
			            		}
			            		
			            	}
		            	}
	            	}
            	
            	
            	synchronized (this){
	            	try {	
					this.wait(300);
					} catch (InterruptedException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
            	}
        }
        //new WaitForUserDialog("Laser Spot Tracking", "The track is finished.").show();
        saveResults(directory);
        Analyzer.setPrecision(defaultPrecision);
    }
	
	private boolean checkJavaCV(String version, boolean treatAsMinVer, String components) {
		
		String javaCVInstallCommand = "Install JavaCV libraries";
    	Hashtable table = Menus.getCommands();
		String javaCVInstallClassName = (String)table.get(javaCVInstallCommand);
		if (javaCVInstallClassName==null) {
//			IJ.showMessage("JavaCV check", "JavaCV Installer not found.\n"
//					+"Please install it from from JavaCVInstaller update site:\n"
//					+"https://sites.imagej.net/JavaCVInstaller/");
			
			int result = JOptionPane.showConfirmDialog(null,
					"<html><h2>JavaCV Installer not found.</h2>"
							+ "<br>Please install it from from JavaCVInstaller update site:"
							+ "<br>https://sites.imagej.net/JavaCVInstaller/"
							+ "<br>Do you whant it to be installed now for you?"
							+ "<br><i>you need to restart ImageJ after the install</i></html>",
							"JavaCV check",
                    JOptionPane.YES_NO_OPTION,
                    JOptionPane.QUESTION_MESSAGE);
			if (result == JOptionPane.YES_OPTION) {
				net.imagej.updater.CommandLine updCmd = new net.imagej.updater.CommandLine(AppUtils.getBaseDirectory("ij.dir", CommandLine.class, "updater"), 80);
				updCmd.addOrEditUploadSite("JavaCVInstaller", "https://sites.imagej.net/JavaCVInstaller/", null, null, false);
				net.imagej.updater.CommandLine updCmd2 = new net.imagej.updater.CommandLine(AppUtils.getBaseDirectory("ij.dir", CommandLine.class, "updater"), 80);
				updCmd2.update(Arrays.asList("plugins/JavaCV_Installer/JavaCV_Installer.jar"));
				IJ.run("Refresh Menus");
				table = Menus.getCommands();
				javaCVInstallClassName = (String)table.get(javaCVInstallCommand);
				if (javaCVInstallClassName==null) {
					IJ.showMessage("JavaCV check", "Failed to install JavaCV Installer plugin.\nPlease install it manually.");
				}
			}
			return false;
		}
		
		String installerCommand = "version="
				+ version
				+ " select_installation_option=[Install missing] "
				+ (treatAsMinVer?"treat_selected_version_as_minimal_required ":"")
				+ components;

		boolean saveRecorder = Recorder.record;		//save state of the macro Recorder
		Recorder.record = false;					//disable the macro Recorder to avoid the JavaCV installer plugin being recorded instead of this plugin
		String saveMacroOptions = Macro.getOptions();
		IJ.run("Install JavaCV libraries", installerCommand);
		if (saveMacroOptions != null) Macro.setOptions(saveMacroOptions);
		Recorder.record = saveRecorder;				//restore the state of the macro Recorder
				
		String result = Prefs.get("javacv.install_result", "");
		String launcherResult = Prefs.get("javacv.install_result_launcher", "");
		if (!(result.equalsIgnoreCase("success") && launcherResult.equalsIgnoreCase("success"))) {
			if(result.indexOf("restart")>-1 || launcherResult.indexOf("restart")>-1) {
				IJ.log("Please restart ImageJ to proceed with installation of necessary JavaCV libraries.");
				return false;
			} else {
				IJ.log("JavaCV installation failed. Trying to use JavaCV as is...");
				return true;
			}
		}
		return true;
	}
	
	private Instant getShotTime(String imageFilePath, int videoSlice)
	{
		 // the creation time of the image is taken from the EXIF metadata
	    
		if (videoInput){
			long timeStampMicroSec = Math.round(Double.parseDouble(stack.getSliceLabel(videoSlice).replaceAll(" s", ""))*1000000);// ((FFmpeg_FrameReader)stack).getFrameTimeStamp(videoSlice - 1);
			if (useTimeStamps) return Instant.ofEpochSecond(0L, timeStampMicroSec*1000L);
			else return Instant.ofEpochSecond(0L, Math.round(1000000000.0*(videoSlice - 1)/impliedFrameRate));
		}
	       
		File jpegFile = new File(imageFilePath);
		
		Metadata metadata;
		
		try {
			metadata = ImageMetadataReader.readMetadata(jpegFile);
			ExifSubIFDDirectory md_directory = metadata.getFirstDirectoryOfType(ExifSubIFDDirectory.class);
		    return md_directory.getDateOriginal().toInstant();//new DateTime(md_directory.getDateOriginal());
			
		} catch (Exception e) {
			setAltTimeMeasure();
			return null;
		}
				
	}
	
	private boolean testMatchResult(double result, double ref, int method, double x, double y, int searchWidth, int tplSize) {
	
		boolean successfulMatch = true;
		double distTrsh=Math.min(0.05*tplSize, 0.05*searchWidth);
		double thrsh=matchThreshold[method];
		switch (method) {
    	case 0:
    		if (result/ref>thrsh) successfulMatch = false;
    		break;
    	case 1:
    		if (result>thrsh) successfulMatch = false;
    		break;
    	case 2:
    		if (Math.abs((result-ref)/ref)>thrsh) successfulMatch = false;
    		break;
    	case 3:
    		if (Math.abs(result-ref)>thrsh) successfulMatch = false;
    		break;
    	case 4:
    		if (Math.abs(result-ref)/ref>thrsh) successfulMatch = false;
    		break;
    	case 5:
    		if (Math.abs(result-ref)>thrsh) successfulMatch = false;
    		break;
		}
		if (searchWidth!=0 &&  ((x<distTrsh) || (y<distTrsh) || (x>searchWidth-distTrsh) || (y>searchWidth-distTrsh))) successfulMatch = false;
		
		
		return successfulMatch;
    
	}
	
	private void adjustThreshold(double result, double ref, int method) {
		
		
		switch (method) {
    	case 0:
    		matchThreshold[method] =1.1*result/ref;
    		break;
    	case 1:
    		matchThreshold[method] =1.1*result;
    		break;
    	case 2:
    	case 4:
    		matchThreshold[method] =1.1*Math.abs((result-ref)/ref);
    		break;
    	case 3:
    	case 5:	
    		matchThreshold[method] =1.1*Math.abs(result-ref);
    		break;
    	
		}
		
    
	}
	
	private int failureQuestionDlg(String placeName) {
		Object[] options1 = { "Keep the result", "Skip the frame",
        "Stop tracking" };
		//String placeName = (place==0?"stable mark":"laser spot");  
		JPanel panel = new JPanel();
		panel.add(new JLabel("<html>Match of the "+placeName+" is poor."
				+ "<br>Select one of the possibilities:"
				+ "<br>1. Accept the match and continue"
				+ "<br>2. Skip this frame and continue"
				+ "<br>3. Stop the tracking</html>"));
		

		imgWindow.toFront();
		int result = JOptionPane.showOptionDialog(null, panel, "Match is poor",
        JOptionPane.YES_NO_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE,
        null, options1, null);
		if (result== JOptionPane.YES_OPTION) return 0;
		if (result== JOptionPane.NO_OPTION) return 1;
		return 2;
	}

    private int analyseSlice(int slice, ImageProcessor slice_proc) {

 
        double[] coord_res = new double[3]; 
        Overlay overlay;
        
        ImagePlus spot_tar = new ImagePlus("",slice_proc);
        ImagePlus mark1_tar = new ImagePlus("",slice_proc);
        ImagePlus mark2_tar = new ImagePlus("",slice_proc);
        ImagePlus mark3_tar = new ImagePlus("",slice_proc);
        ImagePlus mark4_tar = new ImagePlus("",slice_proc);
        
        ImagePlus tmpIp;
        
         int xStart_free=0 ,yStart_free=0, sWX_free=width, sWY_free=height, 
        	 
        	 xStart_mark1=0, yStart_mark1=0, sWX_mark1=width, sWY_mark1=height,
        	 xStart_mark2=0, yStart_mark2=0, sWX_mark2=width, sWY_mark2=height,
        	 xStart_mark3=0, yStart_mark3=0, sWX_mark3=width, sWY_mark3=height,
        	 xStart_mark4=0, yStart_mark4=0, sWX_mark4=width, sWY_mark4=height;
        	 
        
       

        if (sArea != 0) {


        	// Specifying coordinates of the search rectangle around the free end
        	
            xStart_free = spot_rect.x + (int)disX_spot - sArea;
            yStart_free = spot_rect.y + (int)disY_spot - sArea;
            sWX_free = spot_rect.width + 2 * sArea;
            sWY_free = spot_rect.height + 2 * sArea;

            if (xStart_free < 0) {
                xStart_free = 0;
            }
            if (yStart_free < 0) {
                yStart_free = 0;
            }
            if (xStart_free + sWX_free > width) {
                xStart_free = width - sWX_free;
            }
            if (yStart_free + sWY_free > height) {
                yStart_free = height - sWY_free;
            }
            
            // Small image containing free crystal's end
            spot_tar.setRoi(xStart_free, yStart_free, sWX_free, sWY_free);
            spot_tar=spot_tar.crop();
            
            
            
           
            
            
            
			xStart_mark1 = mark1_rect.x + (int)disX_mark1 - sArea;
            yStart_mark1 = mark1_rect.y + (int)disY_mark1 - sArea;
            
            sWX_mark1 = mark1_rect.width + 2 * sArea;
            sWY_mark1 = mark1_rect.height + 2 * sArea;

            if (xStart_mark1 < 0) {
                xStart_mark1 = 0;
            }
            if (yStart_mark1 < 0) {
                yStart_mark1 = 0;
            }
            if (xStart_mark1 + sWX_mark1 > width) {
                xStart_mark1 = width - sWX_mark1;
            }
            if (yStart_mark1 + sWY_mark1 > height) {
                yStart_mark1 = height - sWY_mark1;
            }
            
            // Small image containing needed mark1 part
            mark1_tar.setRoi(xStart_mark1, yStart_mark1, sWX_mark1, sWY_mark1);
            mark1_tar=mark1_tar.crop();
            
            xStart_mark2 = mark2_rect.x + (int)disX_mark2 - sArea;
            yStart_mark2 = mark2_rect.y + (int)disY_mark2 - sArea;
            
            sWX_mark2 = mark2_rect.width + 2 * sArea;
            sWY_mark2 = mark2_rect.height + 2 * sArea;

            if (xStart_mark2 < 0) {
                xStart_mark2 = 0;
            }
            if (yStart_mark2 < 0) {
                yStart_mark2 = 0;
            }
            if (xStart_mark2 + sWX_mark2 > width) {
                xStart_mark2 = width - sWX_mark2;
            }
            if (yStart_mark2 + sWY_mark2 > height) {
                yStart_mark2 = height - sWY_mark2;
            }
            
            // Small image containing needed mark2 part
            mark2_tar.setRoi(xStart_mark2, yStart_mark2, sWX_mark2, sWY_mark2);
            mark2_tar=mark2_tar.crop();
            
            xStart_mark3 = mark3_rect.x + (int)disX_mark3 - sArea;
            yStart_mark3 = mark3_rect.y + (int)disY_mark3 - sArea;
            
            sWX_mark3 = mark3_rect.width + 2 * sArea;
            sWY_mark3 = mark3_rect.height + 2 * sArea;

            if (xStart_mark3 < 0) {
                xStart_mark3 = 0;
            }
            if (yStart_mark3 < 0) {
                yStart_mark3 = 0;
            }
            if (xStart_mark3 + sWX_mark3 > width) {
                xStart_mark3 = width - sWX_mark3;
            }
            if (yStart_mark3 + sWY_mark3 > height) {
                yStart_mark3 = height - sWY_mark3;
            }
            
            // Small image containing needed mark3 part
            mark3_tar.setRoi(xStart_mark3, yStart_mark3, sWX_mark3, sWY_mark3);
            mark3_tar=mark3_tar.crop();
            
            xStart_mark4 = mark4_rect.x + (int)disX_mark4 - sArea;
            yStart_mark4 = mark4_rect.y + (int)disY_mark4 - sArea;
            
            sWX_mark4 = mark4_rect.width + 2 * sArea;
            sWY_mark4 = mark4_rect.height + 2 * sArea;

            if (xStart_mark4 < 0) {
                xStart_mark4 = 0;
            }
            if (yStart_mark4 < 0) {
                yStart_mark4 = 0;
            }
            if (xStart_mark4 + sWX_mark4 > width) {
                xStart_mark4 = width - sWX_mark4;
            }
            if (yStart_mark4 + sWY_mark4 > height) {
                yStart_mark4 = height - sWY_mark4;
            }
            
            // Small image containing needed mark4 part
            mark4_tar.setRoi(xStart_mark4, yStart_mark4, sWX_mark4, sWY_mark4);
            mark4_tar=mark4_tar.crop();
            
            

            
 
        } else {
        	// Needed parts will be searched over the whole slice
           
        }
        
        if (matchIntensity) {
        	ImageConverter ic = new ImageConverter(spot_tar);
        	ic.convertToGray32();
        	ImageConverter mark1_ic = new ImageConverter(mark1_tar);
        	mark1_ic.convertToGray32();
        	ImageConverter mark2_ic = new ImageConverter(mark2_tar);
        	mark2_ic.convertToGray32();
        	ImageConverter mark3_ic = new ImageConverter(mark3_tar);
        	mark3_ic.convertToGray32();
        	ImageConverter mark4_ic = new ImageConverter(mark4_tar);
        	mark4_ic.convertToGray32();
        	
        }
        gaussianBlur.blurGaussian(spot_tar.getProcessor(), 2, 2, 0.02);
        gaussianBlur.blurGaussian(mark1_tar.getProcessor(), 2, 2, 0.02);
        gaussianBlur.blurGaussian(mark2_tar.getProcessor(), 2, 2, 0.02);
        gaussianBlur.blurGaussian(mark3_tar.getProcessor(), 2, 2, 0.02);
        gaussianBlur.blurGaussian(mark4_tar.getProcessor(), 2, 2, 0.02);
        
        
        coord_res = doMatch_coord_res(mark1_tar.getProcessor(), mark1_ref.getProcessor(), method, subPixel, null);
        
        
        boolean ignoreFrame=false, stopTracking=false;
        if (!testMatchResult(coord_res[2], mark1_mideal, method, coord_res[0], coord_res[1], sArea*2, templSize)) { ///////// The holder is not found...
        	/*
			if (sArea!=0) {										  ///////// Let's try global search if it was local search before
			        		
			        		
			        		
			        		xStart_mark1=yStart_mark1=0;        		
			        		ImagePlus full_tar= new ImagePlus("",slice_proc);
			        		if (matchIntensity) {
			        			ImageConverter ic = new ImageConverter(full_tar);
			        			ic.convertToGray32();
			        			
			        		}
			        		gaussianBlur.blurGaussian(full_tar.getProcessor(), 2, 2, 0.02);
			        		coord_res = doMatch_coord_res(full_tar.getProcessor(), mark1_ref.getProcessor(), method, subPixel, null);
			        		if (!testMatchResult(coord_res[2], mark1_mideal, method, coord_res[0], coord_res[1], 0, templSize)) { ////////////// Not found globally
			        			overlay = new Overlay();
			        			if (refBitDepth==24 && !matchIntensity) {
			         				tmpIp = mark1_ref.duplicate();
			         				ImageConverter ic = new ImageConverter(tmpIp);
			        	ic.convertToGray32();
			         			} else tmpIp=mark1_ref;
			        			ImageRoi imageRoi_mark1 = new ImageRoi((int)coord_res[0], (int)coord_res[1],tmpIp.getProcessor());
			        	        imageRoi_mark1.setOpacity(0.3);
			        	        overlay.addElement(imageRoi_mark1);
			        			imp.setSlice(slice);
			        			imp.setOverlay(overlay);
			        			int failureAnswer = failureQuestionDlg(0); 
			        			if (failureAnswer==0) adjustThreshold(coord_res[2], mark1_mideal, method);
			        			ignoreFrame = (failureAnswer==1);
			        			stopTracking = (failureAnswer==2);
			        		} else {												///////////// The mark1 was found shifted. Shift search areas and continue
			        			
			        			        spot_tar = new ImagePlus("",slice_proc);
			        	               	//mid_tar = new ImagePlus("",slice_proc);
			        					double xShift = coord_res[0] - mark1_rect.x - disX_mark1,
			        							yShift = coord_res[1] - mark1_rect.y - disY_mark1;
			
			        					xStart_free += xShift;
			        		            yStart_free += yShift;
			        		            
			
			        		            if (xStart_free < 0) {
			        		                xStart_free = 0;
			        		            }
			        		            if (yStart_free < 0) {
			        		                yStart_free = 0;
			        		            }
			        		            if (xStart_free + sWX_free > width) {
			        		                xStart_free = width - sWX_free;
			        		            }
			        		            if (yStart_free + sWY_free > height) {
			        		                yStart_free = height - sWY_free;
			        		            }
			        		            
			        		            // Small image with spot
			        		            spot_tar.setRoi(xStart_free, yStart_free, sWX_free, sWY_free);
			        		            spot_tar=spot_tar.crop();
			        		            
			        		            
										if (matchIntensity) {
			        		            	ImageConverter ic = new ImageConverter(spot_tar);
			        		            	ic.convertToGray32();
			        		            
			        		            }
			        		            gaussianBlur.blurGaussian(spot_tar.getProcessor(), 2, 2, 0.02);      
			        		            
			        		            
			        		            xStart_mark2 += xShift;
			        		            yStart_mark2 += yShift;
			        		            
			
			        		            if (xStart_mark2 < 0) {
			        		                xStart_mark2 = 0;
			        		            }
			        		            if (yStart_mark2 < 0) {
			        		                yStart_mark2 = 0;
			        		            }
			        		            if (xStart_mark2 + sWX_mark2 > width) {
			        		                xStart_mark2 = width - sWX_mark2;
			        		            }
			        		            if (yStart_mark2 + sWY_mark2 > height) {
			        		                yStart_mark2 = height - sWY_mark2;
			        		            }
			        		            
			        		            mark2_tar = new ImagePlus("",slice_proc);
			        		            // Small image containing mark2 crystal's end
			        		            mark2_tar.setRoi(xStart_mark2, yStart_mark2, sWX_mark2, sWY_mark2);
			        		            mark2_tar=mark2_tar.crop();
			        		            
			        		            
										if (matchIntensity) {
			        		            	ImageConverter ic = new ImageConverter(mark2_tar);
			        		            	ic.convertToGray32();
			        		            
			        		            }
			        		            gaussianBlur.blurGaussian(mark2_tar.getProcessor(), 2, 2, 0.02);   
			        		            
			        		            
			        		            xStart_mark3 += xShift;
			        		            yStart_mark3 += yShift;
			        		            
			
			        		            if (xStart_mark3 < 0) {
			        		                xStart_mark3 = 0;
			        		            }
			        		            if (yStart_mark3 < 0) {
			        		                yStart_mark3 = 0;
			        		            }
			        		            if (xStart_mark3 + sWX_mark3 > width) {
			        		                xStart_mark3 = width - sWX_mark3;
			        		            }
			        		            if (yStart_mark3 + sWY_mark3 > height) {
			        		                yStart_mark3 = height - sWY_mark3;
			        		            }
			        		            
			        		            mark3_tar = new ImagePlus("",slice_proc);
			        		            // Small image containing mark3 crystal's end
			        		            mark3_tar.setRoi(xStart_mark3, yStart_mark3, sWX_mark3, sWY_mark3);
			        		            mark3_tar=mark3_tar.crop();
			        		            
			        		            
										if (matchIntensity) {
			        		            	ImageConverter ic = new ImageConverter(mark3_tar);
			        		            	ic.convertToGray32();
			        		            
			        		            }
			        		            gaussianBlur.blurGaussian(mark3_tar.getProcessor(), 2, 2, 0.02);  
			        		            
			        		            xStart_mark4 += xShift;
			        		            yStart_mark4 += yShift;
			        		            
			
			        		            if (xStart_mark4 < 0) {
			        		                xStart_mark4 = 0;
			        		            }
			        		            if (yStart_mark4 < 0) {
			        		                yStart_mark4 = 0;
			        		            }
			        		            if (xStart_mark4 + sWX_mark4 > width) {
			        		                xStart_mark4 = width - sWX_mark4;
			        		            }
			        		            if (yStart_mark4 + sWY_mark4 > height) {
			        		                yStart_mark4 = height - sWY_mark4;
			        		            }
			        		            
			        		            mark4_tar = new ImagePlus("",slice_proc);
			        		            // Small image containing mark4 crystal's end
			        		            mark4_tar.setRoi(xStart_mark4, yStart_mark4, sWX_mark4, sWY_mark4);
			        		            mark4_tar=mark4_tar.crop();
			        		            
			        		            
										if (matchIntensity) {
			        		            	ImageConverter ic = new ImageConverter(mark4_tar);
			        		            	ic.convertToGray32();
			        		            
			        		            }
			        		            gaussianBlur.blurGaussian(mark4_tar.getProcessor(), 2, 2, 0.02);  
			        		            
			        		            
			        		            
			        		            
			        		            
			        		            
			       		            
			        		}
			        	} else { ///////////////// The search was initially global but the holder was not found 
			        		overlay = new Overlay();
			        		if (refBitDepth==24 && !matchIntensity) {
			     				tmpIp = mark1_ref.duplicate();
			     				ImageConverter ic = new ImageConverter(tmpIp);
			    	ic.convertToGray32();
			     			} else tmpIp=mark1_ref;
			    			ImageRoi imageRoi_mark1 = new ImageRoi((int)coord_res[0], (int)coord_res[1],tmpIp.getProcessor());
			    imageRoi_mark1.setOpacity(0.3);
			    overlay.addElement(imageRoi_mark1);
			    			imp.setSlice(slice);
			    			imp.setOverlay(overlay);
			        		int failureAnswer = failureQuestionDlg(0); 
			        		if (failureAnswer==0) adjustThreshold(coord_res[2], mark1_mideal, method);
			    			ignoreFrame = (failureAnswer==1);
			    			stopTracking = (failureAnswer==2);
			        	}
			*/
        	
        	
        	int sArea_new=sArea;
			boolean newMark1PositionFound=false, leftBound=false, rightBound=false, bottomBound=false, upperBound=false;
			
			if (sArea!=0)
			while(!newMark1PositionFound && !(leftBound && rightBound && bottomBound && upperBound)){
			
				
				sArea_new*=2;
				//IJ.showMessage("Try to find in area = " + sArea_new);
				xStart_mark1 = mark1_rect.x + (int)disX_mark1 - sArea_new;
	            yStart_mark1 = mark1_rect.y + (int)disY_mark1 - sArea_new;
	            sWX_mark1 = mark1_rect.width + 2 * sArea_new;
	            sWY_mark1 = mark1_rect.height + 2 * sArea_new;

	            if (xStart_mark1 < 0) {
	                xStart_mark1 = 0;
	                leftBound=true;
	            }
	            if (yStart_mark1 < 0) {
	                yStart_mark1 = 0;
	                upperBound=true;
	            }
	            if (xStart_mark1 + sWX_mark1 > width) {
	            	sWX_mark1 = width - xStart_mark1;
	                rightBound=true;
	            }
	            if (yStart_mark1 + sWY_mark1 > height) {
	            	sWY_mark1 = height - yStart_mark1;
	                bottomBound=true;
	            }
	            
	            mark1_tar = new ImagePlus("",slice_proc);
	            
	            mark1_tar.setRoi(xStart_mark1, yStart_mark1, sWX_mark1, sWY_mark1);
	            mark1_tar=mark1_tar.crop();
	            
	            if (matchIntensity) {
	            	ImageConverter ic = new ImageConverter(mark1_tar);
	            	ic.convertToGray32();
	            
	            }
	            gaussianBlur.blurGaussian(mark1_tar.getProcessor(), 2, 2, 0.02); 
	            
	            coord_res = doMatch_coord_res(mark1_tar.getProcessor(), mark1_ref.getProcessor(), method, subPixel, null);

    			if (!testMatchResult(coord_res[2], mark1_mideal, method, coord_res[0], coord_res[1], sArea_new*2, templSize)) {
    				
    				
    				if (refBitDepth==24 && !matchIntensity) {
         				tmpIp = mark1_ref.duplicate();
         				ImageConverter ic = new ImageConverter(tmpIp);
                    	ic.convertToGray32();
         			} else tmpIp=mark1_ref;
        			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_mark1, (int)coord_res[1]+ yStart_mark1,tmpIp.getProcessor());
        	        imageRoi.setOpacity(0.3);
        	        overlay = new Overlay();
        	        overlay.addElement(imageRoi);
        			//imp.setSlice(slice);
        			
        			overlay.addElement(new Roi(xStart_mark1, yStart_mark1, sWX_mark1, sWY_mark1));
        			imp.setSlice(slice);
        			imp.setOverlay(overlay);
        			//IJ.showMessage("Not found in Area=" + sArea_new);
    				
    			} else {
    				//IJ.showMessage("Found in Area = " + sArea_new);
    				newMark1PositionFound=true;
    			}
	            
			}
			
			
			
			if (!newMark1PositionFound){
				
				overlay = new Overlay();
				if (refBitDepth==24 && !matchIntensity) {
     				tmpIp = mark1_ref.duplicate();
     				ImageConverter ic = new ImageConverter(tmpIp);
                	ic.convertToGray32();
     			} else tmpIp=mark1_ref;
    			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_mark1, (int)coord_res[1]+ yStart_mark1,tmpIp.getProcessor());
    	        imageRoi.setOpacity(0.3);
    	        overlay.addElement(imageRoi);
    			imp.setSlice(slice);
    			imp.setOverlay(overlay);
				int failureAnswer = failureQuestionDlg("mark1"); 
				if (failureAnswer==0) adjustThreshold(coord_res[2], mark1_mideal, method);
    			ignoreFrame = (failureAnswer==1);
    			stopTracking = (failureAnswer==2);
			} else {
				double xShift = coord_res[0] + xStart_mark1 - mark1_rect.x - disX_mark1,
						yShift = coord_res[1] + yStart_mark1 - mark1_rect.y - disY_mark1;

				xStart_free += xShift;
		        yStart_free += yShift;
		        

		        if (xStart_free < 0) {
		            xStart_free = 0;
		        }
		        if (yStart_free < 0) {
		            yStart_free = 0;
		        }
		        if (xStart_free + sWX_free > width) {
		            xStart_free = width - sWX_free;
		        }
		        if (yStart_free + sWY_free > height) {
		            yStart_free = height - sWY_free;
		        }
		        
		        spot_tar = new ImagePlus("",slice_proc);
		        // Small image with spot
		        spot_tar.setRoi(xStart_free, yStart_free, sWX_free, sWY_free);
		        spot_tar=spot_tar.crop();
		        
		        
				if (matchIntensity) {
		        	ImageConverter ic = new ImageConverter(spot_tar);
		        	ic.convertToGray32();
		        
		        }
		        gaussianBlur.blurGaussian(spot_tar.getProcessor(), 2, 2, 0.02);      
		        
		        
		        xStart_mark2 += xShift;
		        yStart_mark2 += yShift;
		        

		        if (xStart_mark2 < 0) {
		            xStart_mark2 = 0;
		        }
		        if (yStart_mark2 < 0) {
		            yStart_mark2 = 0;
		        }
		        if (xStart_mark2 + sWX_mark2 > width) {
		            xStart_mark2 = width - sWX_mark2;
		        }
		        if (yStart_mark2 + sWY_mark2 > height) {
		            yStart_mark2 = height - sWY_mark2;
		        }
		        
		        mark2_tar = new ImagePlus("",slice_proc);
		        // Small image containing mark2 crystal's end
		        mark2_tar.setRoi(xStart_mark2, yStart_mark2, sWX_mark2, sWY_mark2);
		        mark2_tar=mark2_tar.crop();
		        
		        
				if (matchIntensity) {
		        	ImageConverter ic = new ImageConverter(mark2_tar);
		        	ic.convertToGray32();
		        
		        }
		        gaussianBlur.blurGaussian(mark2_tar.getProcessor(), 2, 2, 0.02);   
		        
		        
		        xStart_mark3 += xShift;
		        yStart_mark3 += yShift;
		        

		        if (xStart_mark3 < 0) {
		            xStart_mark3 = 0;
		        }
		        if (yStart_mark3 < 0) {
		            yStart_mark3 = 0;
		        }
		        if (xStart_mark3 + sWX_mark3 > width) {
		            xStart_mark3 = width - sWX_mark3;
		        }
		        if (yStart_mark3 + sWY_mark3 > height) {
		            yStart_mark3 = height - sWY_mark3;
		        }
		        
		        mark3_tar = new ImagePlus("",slice_proc);
		        // Small image containing mark3 crystal's end
		        mark3_tar.setRoi(xStart_mark3, yStart_mark3, sWX_mark3, sWY_mark3);
		        mark3_tar=mark3_tar.crop();
		        
		        
				if (matchIntensity) {
		        	ImageConverter ic = new ImageConverter(mark3_tar);
		        	ic.convertToGray32();
		        
		        }
		        gaussianBlur.blurGaussian(mark3_tar.getProcessor(), 2, 2, 0.02);  
		        
		        xStart_mark4 += xShift;
		        yStart_mark4 += yShift;
		        

		        if (xStart_mark4 < 0) {
		            xStart_mark4 = 0;
		        }
		        if (yStart_mark4 < 0) {
		            yStart_mark4 = 0;
		        }
		        if (xStart_mark4 + sWX_mark4 > width) {
		            xStart_mark4 = width - sWX_mark4;
		        }
		        if (yStart_mark4 + sWY_mark4 > height) {
		            yStart_mark4 = height - sWY_mark4;
		        }
		        
		        mark4_tar = new ImagePlus("",slice_proc);
		        // Small image containing mark4 crystal's end
		        mark4_tar.setRoi(xStart_mark4, yStart_mark4, sWX_mark4, sWY_mark4);
		        mark4_tar=mark4_tar.crop();
		        
		        
				if (matchIntensity) {
		        	ImageConverter ic = new ImageConverter(mark4_tar);
		        	ic.convertToGray32();
		        
		        }
		        gaussianBlur.blurGaussian(mark4_tar.getProcessor(), 2, 2, 0.02);  
				
			}
        	
        }
        
        if (ignoreFrame) return 1;
        if (stopTracking) return 2;
        
        mark1_matchRes.add(coord_res[2]);
        
        disX_mark1 = coord_res[0] + xStart_mark1 - mark1_rect.x;
        disY_mark1 = coord_res[1] + yStart_mark1 - mark1_rect.y;
        
        //correct first estimation
        if (firstPoint) {
            disX_mark10 = disX_mark1;
            disY_mark10 = disY_mark1;
        }
        
        disX_mark1 -= disX_mark10;
        disY_mark1 -= disY_mark10;
        
       	
		
        
        
        //mark2_mideal= doMatch_test(mark2_ref.getProcessor(),idealMethod);
        coord_res = doMatch_coord_res(mark2_tar.getProcessor(), mark2_ref.getProcessor(), method, subPixel, null);
        
        
        if (!testMatchResult(coord_res[2], mark2_mideal, method, coord_res[0], coord_res[1], sArea*2, templSize)) {
			overlay = new Overlay();
			if (refBitDepth==24 && !matchIntensity) {
 				tmpIp = mark2_ref.duplicate();
 				ImageConverter ic = new ImageConverter(tmpIp);
            	ic.convertToGray32();
 			} else tmpIp=mark2_ref;
			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_mark2, (int)coord_res[1]+ yStart_mark2,tmpIp.getProcessor());
	        imageRoi.setOpacity(0.3);
	        overlay.addElement(imageRoi);
			imp.setSlice(slice);
			imp.setOverlay(overlay);
			int failureAnswer = failureQuestionDlg("mark2"); 
			if (failureAnswer==0) adjustThreshold(coord_res[2], mark2_mideal, method);
			ignoreFrame = (failureAnswer==1);
			stopTracking = (failureAnswer==2);
		}
		
		if (ignoreFrame) return 1;
        if (stopTracking) return 2;

        //if (iter>0) mark2_matchRes.remove(mark2_matchRes.size()-1);
		mark2_matchRes.add(coord_res[2]);
		
		disX_mark2 = coord_res[0] + xStart_mark2 - mark2_rect.x;
        disY_mark2 = coord_res[1] + yStart_mark2 - mark2_rect.y;
        
      //correct first estimation
        if (firstPoint) {
            disX_mark20 = disX_mark2;
            disY_mark20 = disY_mark2;
        }
        
        disX_mark2 -= disX_mark20;
        disY_mark2 -= disY_mark20;
        
        //mark3_mideal= doMatch_test(mark3_ref.getProcessor(),idealMethod);
        coord_res = doMatch_coord_res(mark3_tar.getProcessor(), mark3_ref.getProcessor(), method, subPixel, null);
        
        
        if (!testMatchResult(coord_res[2], mark3_mideal, method, coord_res[0], coord_res[1], sArea*2, templSize)) {
			overlay = new Overlay();
			if (refBitDepth==24 && !matchIntensity) {
 				tmpIp = mark3_ref.duplicate();
 				ImageConverter ic = new ImageConverter(tmpIp);
            	ic.convertToGray32();
 			} else tmpIp=mark3_ref;
			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_mark3, (int)coord_res[1]+ yStart_mark3,tmpIp.getProcessor());
	        imageRoi.setOpacity(0.3);
	        overlay.addElement(imageRoi);
			imp.setSlice(slice);
			imp.setOverlay(overlay);
			int failureAnswer = failureQuestionDlg("mark3"); 
			if (failureAnswer==0) adjustThreshold(coord_res[2], mark3_mideal, method);
			ignoreFrame = (failureAnswer==1);
			stopTracking = (failureAnswer==2);
		}
		
		if (ignoreFrame) return 1;
        if (stopTracking) return 2;

        //if (iter>0) mark3_matchRes.remove(mark3_matchRes.size()-1);
		mark3_matchRes.add(coord_res[2]);
		
		disX_mark3 = coord_res[0] + xStart_mark3 - mark3_rect.x;
        disY_mark3 = coord_res[1] + yStart_mark3 - mark3_rect.y;
        
      //correct first estimation
        if (firstPoint) {
            disX_mark30 = disX_mark3;
            disY_mark30 = disY_mark3;
        }
        
        disX_mark3 -= disX_mark30;
        disY_mark3 -= disY_mark30;
        
        //mark4_mideal= doMatch_test(mark4_ref.getProcessor(),idealMethod);
        coord_res = doMatch_coord_res(mark4_tar.getProcessor(), mark4_ref.getProcessor(), method, subPixel, null);
        
        
        if (!testMatchResult(coord_res[2], mark4_mideal, method, coord_res[0], coord_res[1], sArea*2, templSize)) {
			overlay = new Overlay();
			if (refBitDepth==24 && !matchIntensity) {
 				tmpIp = mark4_ref.duplicate();
 				ImageConverter ic = new ImageConverter(tmpIp);
            	ic.convertToGray32();
 			} else tmpIp=mark4_ref;
			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_mark4, (int)coord_res[1]+ yStart_mark4,tmpIp.getProcessor());
	        imageRoi.setOpacity(0.3);
	        overlay.addElement(imageRoi);
			imp.setSlice(slice);
			imp.setOverlay(overlay);
			int failureAnswer = failureQuestionDlg("mark4"); 
			if (failureAnswer==0) adjustThreshold(coord_res[2], mark4_mideal, method);
			ignoreFrame = (failureAnswer==1);
			stopTracking = (failureAnswer==2);
		}
		
		if (ignoreFrame) return 1;
        if (stopTracking) return 2;

        //if (iter>0) mark4_matchRes.remove(mark4_matchRes.size()-1);
		mark4_matchRes.add(coord_res[2]);
		
		disX_mark4 = coord_res[0] + xStart_mark4 - mark4_rect.x;
        disY_mark4 = coord_res[1] + yStart_mark4 - mark4_rect.y;
        
      //correct first estimation
        if (firstPoint) {
            disX_mark40 = disX_mark4;
            disY_mark40 = disY_mark4;
        }
        
        disX_mark4 -= disX_mark40;
        disY_mark4 -= disY_mark40;
        
        //// not working part of the template update code
        
        //if (updateTemplates)
        //{
        //	holder_ref = new ImagePlus("",tmptar);
        //	holder_ref.setRoi(new Roi(holder_rect.x + disX_holder, holder_rect.y + disY_holder, (double)holder_rect.width, (double)holder_rect.height));
        //    holder_ref=holder_ref.crop();
        //    ImageConverter holder_ic = new ImageConverter(holder_ref);
        //    holder_ic.convertToGray8();
        //    gaussianBlur = new GaussianBlur();
        //    ImageProcessor ip_tmp=holder_ref.getProcessor();
        //    gaussianBlur.blurGaussian(ip_tmp, 2, 2, 0.02);
        	
        //}
        
        
    			spot_tpl = spot_ref.duplicate();
    			
      			
				spot_mideal=doMatch_test(spot_tpl.getProcessor(), (method==0?2:method));
    			coord_res = doMatch_coord_res(spot_tar.getProcessor(), spot_tpl.getProcessor(), method, subPixel, null);

    			if (!testMatchResult(coord_res[2], spot_mideal, method, coord_res[0], coord_res[1], sArea*2, templSize)) {
    				
    				
    				//IJ.showMessage("Spot is lost");
    				
    				int sArea_new=sArea;
    				boolean newSpotPositionFound=false, leftBound=false, rightBound=false, bottomBound=false, upperBound=false;
    				
    				if (sArea!=0)
    				while(!newSpotPositionFound && !(leftBound && rightBound && bottomBound && upperBound)){
    				
    					
    					sArea_new*=2;
    					if (autoSkip && maxSArea!=0 && sArea_new>maxSArea) break;
    					//IJ.showMessage("Try to find in area = " + sArea_new);
    					xStart_free = spot_rect.x + (int)disX_spot - sArea_new;
    		            yStart_free = spot_rect.y + (int)disY_spot - sArea_new;
    		            sWX_free = spot_rect.width + 2 * sArea_new;
    		            sWY_free = spot_rect.height + 2 * sArea_new;

    		            if (xStart_free < 0) {
    		                xStart_free = 0;
    		                leftBound=true;
    		            }
    		            if (yStart_free < 0) {
    		                yStart_free = 0;
    		                upperBound=true;
    		            }
    		            if (xStart_free + sWX_free > width) {
    		            	sWX_free = width - xStart_free;
    		                rightBound=true;
    		            }
    		            if (yStart_free + sWY_free > height) {
    		            	sWY_free = height - yStart_free;
    		                bottomBound=true;
    		            }
    		            
    		            spot_tar = new ImagePlus("",slice_proc);
    		            
    		            spot_tar.setRoi(xStart_free, yStart_free, sWX_free, sWY_free);
    		            spot_tar=spot_tar.crop();
    		            
    		            if (matchIntensity) {
    		            	ImageConverter ic = new ImageConverter(spot_tar);
    		            	ic.convertToGray32();
    		            
    		            }
    		            gaussianBlur.blurGaussian(spot_tar.getProcessor(), 2, 2, 0.02); 
    		            
    		            coord_res = doMatch_coord_res(spot_tar.getProcessor(), spot_tpl.getProcessor(), method, subPixel, null);

    	    			if (!testMatchResult(coord_res[2], spot_mideal, method, coord_res[0], coord_res[1], sArea_new*2, templSize)) {
    	    				
    	    				
    	    				if (refBitDepth==24 && !matchIntensity) {
    	         				tmpIp = spot_tpl.duplicate();
    	         				ImageConverter ic = new ImageConverter(tmpIp);
    	                    	ic.convertToGray32();
    	         			} else tmpIp=spot_tpl;
    	        			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_free, (int)coord_res[1]+ yStart_free,tmpIp.getProcessor());
    	        	        imageRoi.setOpacity(0.3);
    	        	        overlay = new Overlay();
    	        	        overlay.addElement(imageRoi);
    	        			//imp.setSlice(slice);
    	        			
    	        			overlay.addElement(new Roi(xStart_free, yStart_free, sWX_free, sWY_free));
    	        			imp.setSlice(slice);
    	        			imp.setOverlay(overlay);
    	        			//IJ.showMessage("Not found in Area=" + sArea_new);
    	    				
    	    			} else {
    	    				//IJ.showMessage("Found in Area = " + sArea_new);
    	    				newSpotPositionFound=true;
    	    			}
    		            
    				}
    				
    				
    				
    				if (!newSpotPositionFound){
    					
	    				overlay = new Overlay();
	    				if (refBitDepth==24 && !matchIntensity) {
	         				tmpIp = spot_tpl.duplicate();
	         				ImageConverter ic = new ImageConverter(tmpIp);
	                    	ic.convertToGray32();
	         			} else tmpIp=spot_tpl;
	        			ImageRoi imageRoi = new ImageRoi((int)coord_res[0] + xStart_free, (int)coord_res[1]+ yStart_free,tmpIp.getProcessor());
	        	        imageRoi.setOpacity(0.3);
	        	        overlay.addElement(imageRoi);
	        			imp.setSlice(slice);
	        			imp.setOverlay(overlay);
	        			if (!autoSkip){
		    				int failureAnswer = failureQuestionDlg("laser spot"); 
		    				if (failureAnswer==0) adjustThreshold(coord_res[2], spot_mideal, method);
		        			ignoreFrame = (failureAnswer==1);
		        			stopTracking = (failureAnswer==2);
	        			} else {
	        				ignoreFrame=true;
	        			}
    				}
        		}
    			
    			if (ignoreFrame) {
    				if (!autoSkip && autoSkipCounter++==2) {
    					autoSkipCounter=0;
    					GenericDialog gd = new GenericDialog("Automatic Frame Skip");
    			        gd.addMessage("It's time to think of automatic skip possibility...\n"//
    			        		+"Bad frames will be skipped until the spot is found.\n"//
    			        		+"Maximal size of the search area can be specified to save time.\n"//
    			        		+"Default is 10*(initial search area), zero is for no limit");
    			       
    			        gd.addNumericField("Maximal size of the search area", sArea*10, 0);
    			        
    			        gd.showDialog();
    			        if (gd.wasOKed()) autoSkip=true;
    			        
    			        maxSArea=(int) gd.getNextNumber();
    			        
    				}
    				return 1;
    			}
    	        if (stopTracking) return 2;
 
    	        //if (iter>0) spot_matchRes.remove(spot_matchRes.size()-1);
    	        autoSkip=alwaysAutoSkip;
    	        autoSkipCounter=0;
    			spot_matchRes.add(coord_res[2]);
    			
    			disX_spot = coord_res[0] + xStart_free - spot_rect.x;
                disY_spot = coord_res[1] + yStart_free - spot_rect.y;
    			
              //correct first estimation
                if (firstPoint) {
                    disX_spot0 = disX_spot;
                    disY_spot0 = disY_spot;
                }
                
                disX_spot -= disX_spot0;
                disY_spot -= disY_spot0;
            
            
            if(!firstPoint) anStep++;
			calcDisplacement();
			
			x_pix_list.add(refX_spot+disX_spot-disX_mark1);
			y_pix_list.add(refY_spot+disY_spot-disY_mark1);
		
        
        // the creation time of the image is taken from the EXIF metadata or incremented by timeStep
        
//        if (ExifTime)
//        {
//             Instant shot_time = getShotTime(imp.getOriginalFileInfo().directory + stack.getSliceLabel(slice));
//             		 
//        	if (shot_time!=null) seconds = Duration.between(first_shot_time, shot_time).toNanos()/1000000000.0;//(double)((new Duration(first_shot_time,shot_time)).getStandardSeconds());
//        	else 
//        	{	
//        		ExifTime=false;
//        		if (seconds!=0.0) seconds+=timeStep;
//        	}
//        }
//        else seconds+=timeStep;
			
		if (exifTime)
        {
        	Instant shot_time;
        	if(videoInput) shot_time = getShotTime("", slice);
        	else shot_time = getShotTime(Paths.get(imp.getOriginalFileInfo().directory, stack.getSliceLabel(slice)).toString(), slice);
        	 
        	if (shot_time!=null) seconds = Duration.between(first_shot_time, shot_time).toNanos()/1000000000.0;//(new Duration(first_shot_time,shot_time)).getMillis()/1000.0;
        	else 
        	{	
        		exifTime=false;
        		if (seconds!=0.0) seconds+=timeStep;
        	}
        }
        else seconds+=timeStep;
		
		
		
  
        if (refBitDepth==24 && !matchIntensity) {
				tmpIp = spot_tpl.duplicate();
				ImageConverter ic = new ImageConverter(tmpIp);
            	ic.convertToGray32();
			} else tmpIp=spot_tpl;
        ImageRoi imageRoi_spot = new ImageRoi((int)disX_spot+spot_rect.x, (int)disY_spot+spot_rect.y,tmpIp.getProcessor());
        imageRoi_spot.setOpacity(0.3);
        overlay = new Overlay(imageRoi_spot);
        proi_spot = new PointRoi(refX_spot+disX_spot,refY_spot+disY_spot);
        proi_spot.setPointType(3);
        overlay.addElement(proi_spot);
        
        if (refBitDepth==24 && !matchIntensity) {
			tmpIp = mark1_ref.duplicate();
			ImageConverter ic = new ImageConverter(tmpIp);
        	ic.convertToGray32();
		} else tmpIp=mark1_ref;
        ImageRoi imageRoi_mark1 = new ImageRoi((int)disX_mark1+mark1_rect.x, (int)disY_mark1+mark1_rect.y,tmpIp.getProcessor());
        imageRoi_mark1.setOpacity(0.3);
        overlay.addElement(imageRoi_mark1);
        proi_mark1 = new PointRoi(refX_mark1+disX_mark1,refY_mark1+disY_mark1);
        proi_mark1.setPointType(3);
        overlay.addElement(proi_mark1);
        
        
        if (refBitDepth==24 && !matchIntensity) {
			tmpIp = mark2_ref.duplicate();
			ImageConverter ic = new ImageConverter(tmpIp);
        	ic.convertToGray32();
		} else tmpIp=mark2_ref;
        ImageRoi imageRoi_mark2 = new ImageRoi((int)disX_mark2+mark2_rect.x, (int)disY_mark2+mark2_rect.y,tmpIp.getProcessor());
        imageRoi_mark2.setOpacity(0.3);
        overlay.addElement(imageRoi_mark2);
        proi_mark2 = new PointRoi(refX_mark2+disX_mark2,refY_mark2+disY_mark2);
        proi_mark2.setPointType(3);
        overlay.addElement(proi_mark2);
        
        
        
        if (refBitDepth==24 && !matchIntensity) {
			tmpIp = mark3_ref.duplicate();
			ImageConverter ic = new ImageConverter(tmpIp);
        	ic.convertToGray32();
		} else tmpIp=mark3_ref;
        ImageRoi imageRoi_mark3 = new ImageRoi((int)disX_mark3+mark3_rect.x, (int)disY_mark3+mark3_rect.y,tmpIp.getProcessor());
        imageRoi_mark3.setOpacity(0.3);
        overlay.addElement(imageRoi_mark3);
        proi_mark3 = new PointRoi(refX_mark3+disX_mark3,refY_mark3+disY_mark3);
        proi_mark3.setPointType(3);
        overlay.addElement(proi_mark3);
        
        
        if (refBitDepth==24 && !matchIntensity) {
			tmpIp = mark4_ref.duplicate();
			ImageConverter ic = new ImageConverter(tmpIp);
        	ic.convertToGray32();
		} else tmpIp=mark4_ref;
        ImageRoi imageRoi_mark4 = new ImageRoi((int)disX_mark4+mark4_rect.x, (int)disY_mark4+mark4_rect.y,tmpIp.getProcessor());
        imageRoi_mark4.setOpacity(0.3);
        overlay.addElement(imageRoi_mark4);
        proi_mark4 = new PointRoi(refX_mark4+disX_mark4,refY_mark4+disY_mark4);
        proi_mark4.setPointType(3);
        overlay.addElement(proi_mark4);
 
		overlay.addElement(new Roi(xStart_mark1, yStart_mark1, sWX_mark1, sWY_mark1));
		overlay.addElement(new Roi(xStart_mark2, yStart_mark2, sWX_mark2, sWY_mark2));
		overlay.addElement(new Roi(xStart_mark3, yStart_mark3, sWX_mark3, sWY_mark3));
		overlay.addElement(new Roi(xStart_mark4, yStart_mark4, sWX_mark4, sWY_mark4));
       
        overlay.addElement(new Roi(xStart_free, yStart_free, sWX_free, sWY_free));
        float[] xpf=new float[anStep+1], ypf=new float[anStep+1];
        for (int displStep=0;displStep<anStep+1;displStep++)
        {
        	
        	xpf[displStep]=x_pix_list.get(displStep).floatValue()+(float)disX_mark1;
        	ypf[displStep]=y_pix_list.get(displStep).floatValue()+(float)disY_mark1;
        	
        	
        }
        PolygonRoi needle_line=new PolygonRoi(xpf,ypf,Roi.FREELINE);
        /*
		FloatPolygon flPol = needle_line.getFloatPolygon();
				int nPoints=flPol.npoints;
				String msgstr="xPoins: ";
				for (int pp=0;pp<nPoints;pp++)
		{
			msgstr+=" "+flPol.xpoints[pp];
		}
				IJ.showMessage(msgstr);
				
		*/
        overlay.addElement(needle_line);
		imp.setSlice(slice);
        imp.setOverlay(overlay);
 
        return 0;
    }
    
    private void calcDisplacement() {
    	
    	
		dX_pix=disX_spot-disX_mark1;
        dY_pix=disY_spot-disY_mark1;
        
        double  m1x=refX_mark1+disX_mark1,m1y=refY_mark1+disY_mark1,
        		m2x=refX_mark2+disX_mark2,m2y=refY_mark2+disY_mark2,
        		m3x=refX_mark3+disX_mark3,m3y=refY_mark3+disY_mark3,
        		m4x=refX_mark4+disX_mark4,m4y=refY_mark4+disY_mark4,
       
        /*
		ax=m4x-m1x,ay=m4y-m1y,
		bx=m2x-m1x,by=m2y-m1y,
		cx=m1x+m3x-m2x-m4x,cy=m1y+m3y-m2y-m4y,
		a_invX,a_invY,a_inv_mod,
		b_invX,b_invY,b_inv_mod,
		rx=refX_spot+disX_spot-m1x, ry=refY_spot+disY_spot-m1y;
				a_inv_mod=ax*by-ay*bx;
				b_inv_mod=a_inv_mod;
				a_invX=by/a_inv_mod;
				a_invY=-bx/a_inv_mod;
				b_invX=-ay/a_inv_mod;
				b_invY=ax/a_inv_mod;
		*/
        	   a1x=m4x-m1x,a1y=m4y-m1y,
               b1x=m2x-m1x,b1y=m2y-m1y,
               a2x=m3x-m2x,a2y=m3y-m2y,
               b2x=m3x-m4x,b2y=m3y-m4y,
               
               rx=refX_spot+disX_spot-m1x, ry=refY_spot+disY_spot-m1y,
               
               AX=a1x*(b1y-b2y)+a1y*(b2x-b1x),
               BX=-a1x*b1y+a1y*b1x - rx*(b1y-b2y)-ry*(b2x-b1x),
               CX=-rx*b1y+ry*b1x,
               
               
               AY=b1x*(a1y-a2y)+b1y*(a2x-a1x),
               BY=-b1x*a1y+b1y*a1x - rx*(a1y-a2y)-ry*(a2x-a1x),
               CY=-rx*a1y+ry*a1x;
        
        //double X_abs_new, Y_abs_new;
        
        if (AX==0.0) {
        	x_abs=CX/BX*markDist;
        	y_abs=CY/BY*markDist;
        } else {
        	double DX=Math.sqrt(BX*BX+4.0*AX*CX),
        			DY=Math.sqrt(BY*BY+4.0*AY*CY);
        	x_abs=(DX-BX)/AX/2.0*markDist;
        	y_abs=(-DY-BY)/AY/2.0*markDist;
        }
        
        
        //X_abs=(rx*a_invX+ry*a_invY)*(1.0-(cx*a_invX+cy*a_invY)*(rx*b_invX+ry*b_invY))*markDist;
        //Y_abs=(rx*b_invX+ry*b_invY)*(1.0-(cx*b_invX+cy*b_invY)*(rx*a_invX+ry*a_invY))*markDist;
        
        if (firstPoint) {
        	spotX0=x_abs;
        	spotY0=y_abs;
        	firstPoint=false;
        }
        
        dX=x_abs-spotX0;
        dY=y_abs-spotY0;
        
        
        dL=Math.sqrt(dX*dX+dY*dY);
        //if (dX<0) dL=-dL;
        
    }

 

	
    private boolean getUserParameters() {

    	//get saved parameters
    	method = (int) Prefs.get("laserspottrack.matchMethod", matchMethodDefault);
    	alwaysAutoSkip = (boolean) Prefs.get("laserspottrack.autoSkip", autoSkipDefault);
    	sArea = (int) Prefs.get("laserspottrack.searchArea", searchAreaDefault);
    	templSize = (int) Prefs.get("laserspottrack.templateSize", templSizeDefault);
    	markDist = (double) Prefs.get("laserspottrack.markDist", markDistDefault);
    	matchIntensity = (boolean) Prefs.get("laserspottrack.matchIntensity", matchIntensityDefault);
    	subPixel = (boolean) Prefs.get("laserspottrack.subPixel", subPixelDefault);
    	
        String[] methods = {"Square difference", "Normalized square difference", "Cross correlation", "Normalized cross correlation", "Correlation coefficient", "Normalized correlation coefficient"};
        //String[] itpMethods = {"Bilinear", "Bicubic"};

        GenericDialog gd = new GenericDialog(pluginName);
        gd.addMessage("Only virtual stacks of time lapse images are supported currently.\n"
        		+ "Adjust the settings and follow the instructions to select templates to track.");
        gd.addChoice("Matching method", methods, methods[method]);
        gd.addNumericField("Template rectangle size (rectangle ROI size in pixels) ", templSize, 0);
        //gd.addMessage("(Template will be searched on the whole image if search area =0)");
        gd.addNumericField("Search area(pixels around ROI) ", sArea, 0);
        gd.addNumericField("Distance between marks in mm ", markDist, 0);
        gd.addMessage("(Template will be searched on the whole image if search area =0)");
        gd.addCheckbox("Subpixel registration", subPixel);
        gd.addCheckbox("Match RGB images using intensity", matchIntensity);
        gd.addCheckbox("Always skip frames with bad match", alwaysAutoSkip);
        //gd.addChoice("Interpolation method for subpixel translation", itpMethods, itpMethods[itpMethod]);
       
        //gd.addCheckbox("update templates?", false);
        gd.showDialog();
        if (gd.wasCanceled()) {
            return false;
        }
        method = gd.getNextChoiceIndex();
        templSize=(int) gd.getNextNumber();
        sArea = (int) gd.getNextNumber();
        markDist = gd.getNextNumber();
        subPixel = gd.getNextBoolean();
        matchIntensity  = gd.getNextBoolean();
        alwaysAutoSkip = gd.getNextBoolean();
        //itpMethod = gd.getNextChoiceIndex();
        //updateTemplates = gd.getNextBoolean();
        showRT = true;

        //save parameters
        Prefs.set("laserspottrack.matchMethod", method);
        Prefs.set("laserspottrack.autoSkip", alwaysAutoSkip);
    	Prefs.set("laserspottrack.searchArea", sArea);
    	Prefs.set("laserspottrack.templateSize", templSize);
    	Prefs.set("laserspottrack.markDist", markDist);
    	Prefs.set("laserspottrack.matchIntensity", matchIntensity);
    	Prefs.set("laserspottrack.subPixel", subPixel);
    	
        
        return true;
    }
    
    private String setProjectNameDlg()
    {
        GenericDialog projectNameDialog = new GenericDialog(pluginName);
        projectNameDialog.addMessage("Set the name of the project to use it for autonaming and saving result files.\n"
                + "Live empty for manual saving.");
        String lastProject = Prefs.get("laserspottrack.lastProject", "");
        projectNameDialog.addStringField("Project name (short description)", lastProject, 32);
        projectNameDialog.showDialog();
        if(projectNameDialog.wasCanceled()) return "";
        return projectNameDialog.getNextString().trim();
    }
    
    private boolean isValidProjectename(String name) {
        return !Pattern.compile(INVALID_CHARACTERS).matcher(name).find();
    }
    
    private void saveResults(String directory)
    {
        boolean goodName = false;
        String resultsPath = "", plotPath = "";
        while (!goodName) {
            projectName = setProjectNameDlg();
            if (projectName.isEmpty()) 
            {
                //new WaitForUserDialog(pluginName, "Do not forget to save results!").show();
                return;
            }
            if (!isValidProjectename(projectName)) {
                new WaitForUserDialog(pluginName, "Specified name contains forbidden symbols: " + INVALID_CHARACTERS).show();
                continue;
            }
            resultsPath = Paths.get(directory, "Results - " + projectName + ".txt").toString();
            plotPath = Paths.get(directory, "Displacement plot - " + projectName + ".tif").toString();
            if (!new File(resultsPath).exists() && !new File(plotPath).exists()) goodName = true;
            else new WaitForUserDialog(pluginName, "Specified name already exits. Change name or check files!").show();
            Prefs.set("laserspottrack.lastProject", projectName);
        }
        
        rt.save(resultsPath);
        Analyzer.setUnsavedMeasurements(false);
        FileSaver plotSaver = new FileSaver(plotImage);
        
        plotSaver.saveAsTiff(plotPath);
        FileWriter writer;
        try {
            String resultsListPath = Paths.get(directory, "results_list.txt").toString();
            writer = new FileWriter(resultsListPath, true);
            writer.write("Results - " + projectName + ".txt Source: " + imp.getOriginalFileInfo().fileName + "\n");
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
        
    }
    
    /*
	public static IplImage toIplImage(BufferedImage bufImage) {

	    ToIplImage iplConverter = new OpenCVFrameConverter.ToIplImage();
	    Java2DFrameConverter java2dConverter = new Java2DFrameConverter();
	    IplImage iplImage = iplConverter.convert(java2dConverter.convert(bufImage));
	    return iplImage;
	}
	*/
	public static Mat toMatcv(BufferedImage bufImage) {

		Mat mat =  Java2DFrameUtils.toMat(bufImage);
//	    ToMat matConverter = new OpenCVFrameConverter.ToMat();
//	    Java2DFrameConverter java2dConverter = new Java2DFrameConverter();
//	    Mat mat =  matConverter.convert(java2dConverter.convert(bufImage));
	    return mat;
	}
	

    
    public static double[]  doMatch_coord_res(ImageProcessor src, ImageProcessor tpl, int method, boolean subPix, double[] searchLine) {

        BufferedImage bi = null, bi2 = null;
        Mat sourceMat, templateMat, temp, temp2;
        int srcW = src.getWidth();
        int srcH = src.getHeight();
        int tplW = tpl.getWidth();
        int tplH = tpl.getHeight();
        sourceMat = null;
        templateMat = null;
        double[] coord_res = new double[3];
        
        switch (src.getBitDepth()) {
    
            case 16:
                //since cvMatchTemplate don't accept 16bit image, we have to convert it to 32bit
                bi = ((ShortProcessor) src).get16BitBufferedImage();
                temp = toMatcv(bi);
                temp.convertTo(sourceMat, CV_32FC1, 1 / 65535.0, 0);
                bi2 = ((ShortProcessor) tpl).get16BitBufferedImage();
                temp2 = toMatcv(bi2);
                temp2.convertTo(templateMat, CV_32FC1, 1 / 65535.0, 0);
                break;
            case 32:   
            case 24:	
            case 8:
            	
                bi = src.getBufferedImage();
                sourceMat = toMatcv(bi);

                bi2 = tpl.getBufferedImage();
                templateMat = toMatcv(bi2);

                break;
            default:
                IJ.error("Unsupported image type");
                break;
        }

       
        
        Mat resMat = new Mat(new Size(srcW - tplW + 1, srcH - tplH + 1), CV_32FC1);
        

        
        //CV_TM_SQDIFF        = 0,
        //CV_TM_SQDIFF_NORMED = 1,
        //CV_TM_CCORR         = 2,
        //CV_TM_CCORR_NORMED  = 3,
        //CV_TM_CCOEFF        = 4,
        //CV_TM_CCOEFF_NORMED = 5;
         

        ///
        /// This is the template matching function from the cv library 
        ///
       
        //cvMatchTemplate(iplSrc, iplTpl, res, method);
        matchTemplate(sourceMat, templateMat, resMat, method);
        
        //////Search the location of the template
        
        
        FloatIndexer resVal = resMat.createIndexer();
        if (searchLine!=null && !(searchLine[2]==0.0 && searchLine[3]==0.0)){  //////////////////// Searching the middle part along the normal line
        	
        	int[] coord = new int[2];
            coord[0]=0;
            coord[1]=0;
            double minmax=0.0;
            boolean firstPointFound=false;
            int sWh, sWw;
            sWh = resMat.rows();
            sWw = resMat.cols();
            double x0=searchLine[0], y0=searchLine[1], dx0=searchLine[2], dy0=searchLine[3];
            boolean searchMin = (method == 0 || method == 1);
            if (Math.abs(dx0)>Math.abs(dy0))
            {
            	for (int col = 0; col < sWw; col++) {
                	int row = (int)(y0 + dy0*(col-x0)/dx0);
                	if (row>=0 && row < sWh)
                	{
                		double val=resVal.get(row, col);
                		if (!firstPointFound) {
                			firstPointFound = true;
                			minmax=val;
                			coord[0] = col;
     	                    coord[1] = row;
                		}
    	                if ((searchMin && val < minmax) || (!searchMin && val > minmax)) {
    	                    minmax = val;
    	                    coord[0] = col;
    	                    coord[1] = row;
    	                }
                	}
                }
            	
            } else {
            	for (int row = 0; row < sWh; row++) {
                	int col = (int)(x0 + dx0*(row-y0)/dy0);
                	if (col>=0 && col < sWw)
                	{
                		double val=resVal.get(row, col);
                		if (!firstPointFound) {
                			firstPointFound = true;
                			minmax=val;
                			coord[0] = col;
     	                    coord[1] = row;
                		}
    	                if ((searchMin && val < minmax) || (!searchMin && val > minmax)) {
    	                    minmax = val;
    	                    coord[0] = col;
    	                    coord[1] = row;
    	                }
                	}
                }
            }
            coord_res[0] = coord[0];
        	coord_res[1] = coord[1];
        	coord_res[2] = minmax;
        	
        	if (subPix){
            	double dx, dy;
            	int x = (int)coord_res[0], y = (int)coord_res[1]; 
            	double lineAngle = Math.atan2(dy0, dx0), sin = Math.sin(lineAngle), cos = Math.cos(lineAngle);
                
                // border values
                if (x == 0
                        || x == resMat.cols() - 1
                        || y == 0
                        || y == resMat.rows() - 1) {
                    dx = 0.0;
                    dy = 0.0;
                } else {
                	
                	double fxx=resVal.get(y, x - 1) - 2.0 * resVal.get( y, x) + resVal.get(y, x + 1),
                		   fyy=resVal.get(y - 1, x) - 2.0 * resVal.get( y, x) + resVal.get(y + 1, x),
                		   fxy=(resVal.get(y + 1, x + 1) + resVal.get(y - 1, x - 1)
                		   		- resVal.get(y - 1, x + 1) - resVal.get(y + 1, x - 1))/4.0,
                		   fx=(resVal.get(y, x + 1) - resVal.get(y, x - 1))/2.0,
                		   fy=(resVal.get(y + 1, x) - resVal.get(y - 1, x))/2.0,
                		   fr=fx*cos + fy*sin,
                		   frr=fxx*cos*cos + fyy*sin*sin + fxy*sin*cos;
                	
                	if (frr==0.0) {
                		dx = 0.0;
                		dy = 0.0;
                	} else {
                		 dx = -fr/frr*cos;
                         dy = -fr/frr*sin;
                         if (Math.abs(dx)>1.0 || Math.abs(dy)>1.0) {
                        	dx = 0.0;
                     		dy = 0.0;
                         }
                	}
                		
                   
                }
                coord_res[0]+=dx;
                coord_res[1]+=dy;
            }
            
        	
        } else { /////////////////// Searching matching position inside the search area
        	DoublePointer minVal= new DoublePointer(0.0);
        	DoublePointer maxVal= new DoublePointer(0.0);
            Point min = new  Point();
            Point max = new  Point();
            minMaxLoc(resMat, minVal, maxVal, min, max, null);
            if (method == 0 || method == 1) {
            	coord_res[0] = min.x();
            	coord_res[1] = min.y();
            	coord_res[2] = minVal.get();
            } else {
            	coord_res[0] = max.x();
            	coord_res[1] = max.y();
            	coord_res[2] = maxVal.get();
            }
            
            if (subPix){
            	double dx, dy;
            	int x = (int)coord_res[0], y = (int)coord_res[1]; 
                
                // border values
                if (x == 0
                        || x == resMat.cols() - 1
                        || y == 0
                        || y == resMat.rows() - 1) {
                    dx = 0.0;
                    dy = 0.0;
                } else {
                	
                	double fxx=resVal.get(y, x - 1) - 2.0 * resVal.get( y, x) + resVal.get(y, x + 1),
                		   fyy=resVal.get(y - 1, x) - 2.0 * resVal.get( y, x) + resVal.get(y + 1, x),
                		   fxy=(resVal.get(y + 1, x + 1) + resVal.get(y - 1, x - 1)
                		   		- resVal.get(y - 1, x + 1) - resVal.get(y + 1, x - 1))/4.0,
                		   fx=(resVal.get(y, x + 1) - resVal.get(y, x - 1))/2.0,
                		   fy=(resVal.get(y + 1, x) - resVal.get(y - 1, x))/2.0;
                	double denom = fxy*fxy - fxx*fyy;
                	if (denom==0.0) {
                		dx = 0.0;
                		dy = 0.0;
                	} else {
                		 dx = (fyy*fx - fxy*fy)/denom;
                         dy = (fxx*fy - fxy*fx)/denom;
                         if (Math.abs(dx)>1.0 || Math.abs(dy)>1.0) {
                        	dx = 0.0;
                     		dy = 0.0;
                         }
                	}
                		
                   
                }
                coord_res[0]+=dx;
                coord_res[1]+=dy;
            }
        	
        }
        
        return coord_res;
    }
     
    public static double doMatch_test(ImageProcessor src, int method) {

    	
    	
    	
    	BufferedImage bi = null;
    	//bi = src.getBufferedImage();
    	//Mat sourceMat = toMatcv(bi);
    	
        Mat sourceMat, temp;
        sourceMat = null;
        
    	
    	switch (src.getBitDepth()) {
    	             
    	            case 16:
    	            	
    	                
    	                bi = ((ShortProcessor) src).get16BitBufferedImage();
    	                temp = toMatcv(bi);
    	                temp.convertTo(sourceMat, CV_32FC1, 1 / 65535.0, 0);
    	                break;
    	            case 32: 
    	            case 24:	
    	            case 8:
    	            	
    	                bi = src.getBufferedImage();
    	                sourceMat = toMatcv(bi);
    	                break;
    	            default:
    	                IJ.error("Unsupported image type");
    	                break;
    	        }
    	
    	
    	
        
       Size size = new Size(1, 1);
       Mat result = new Mat(size, CV_32FC1);
       matchTemplate(sourceMat, sourceMat, result, method);
       FloatIndexer idx = result.createIndexer(); 
       return idx.get(0);
       
    }
    


	@Override
	public boolean dialogItemChanged(GenericDialog arg0, AWTEvent arg1) {
		if (arg0.wasOKed() || arg0.wasCanceled()) folderMonitoring=true;
		
		return true;
	}
    
}
